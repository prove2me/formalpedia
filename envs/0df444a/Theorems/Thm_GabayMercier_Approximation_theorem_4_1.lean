-- Prove2me | Theorems.Thm_GabayMercier_Approximation_theorem_4_1
-- name    : GabayMercier.Approximation.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:37.253985+00:00
-- url     : https://prove2.me/theorems/e9447951-db04-491a-9db1-66f569b8e21e
-- title:
--   Theorem 4.1 — strong convergence of internal approximations
-- statement:
--   Let $V,Y$ be real Hilbert spaces, $A:V\to Y$ continuous linear, $b\in V'$, and $f_2:Y\to(-\infty,+\infty]$ proper, convex and lower semicontinuous. Assume the paper's standing hypotheses (2.4) and (2.5), feasibility of $({\cal P})$, and the internal approximation conditions (4.1) and (4.3) for finite dimensional $V_k\subseteq V$ and continuous linear maps $A_k:V_k\to Y$. With $f(y)=\frac12\|y\|^2+f_2(y)$, the continuous problem has a unique solution $v^*$; for all sufficiently large $k$, the discrete problem has a unique solution $v_k^*$; and
--   $$
--   v_k^*\longrightarrow v^*\quad\text{strongly in }V.
--   $$
--   The claim is for every eventual selection of discrete solutions, since the first finitely many problems need not be feasible.
--
--   **Formalization Note** The paper prints convergence “in $V_h$”; varying $V_h$ is embedded in the common space $V$. Its proof requires a finite-valued feasible point of $({\cal P})$, stated explicitly here. (4.3) only guarantees discrete feasibility eventually. The $Y_h$ codomain is suppressed because its inclusion in $Y$ is all the theorem uses. The limit $h\to0$ is represented by $k\to\infty$.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 21, Theorem 4.1

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 4.1: eventual unique discrete solutions converge strongly in `V`. -/
theorem theorem_4_1 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) :
    (∃! vs : V, GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs) ∧
    ∀ vs : V, GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs →
      (∀ᶠ k in atTop, ∃! w : Vh k, IsSolutionH (Ah k) f₂ b w) ∧
      ∀ vh : (k : ℕ) → Vh k, (∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k)) →
        Tendsto (fun k => (vh k : V)) atTop (𝓝 vs) := by sorry

end GabayMercier.Approximation
