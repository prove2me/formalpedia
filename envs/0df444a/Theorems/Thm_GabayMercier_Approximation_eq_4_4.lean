-- Prove2me | Theorems.Thm_GabayMercier_Approximation_eq_4_4
-- name    : GabayMercier.Approximation.eq_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:26.120767+00:00
-- url     : https://prove2.me/theorems/daab8d41-7e27-4b21-b909-571378d5087f
-- title:
--   Equation (4.4) — variational characterization of a discrete minimizer
-- statement:
--   Under the standing assumptions and (4.1)–(4.3), fix a finite dimensional $V_k\subseteq V$ with operator $A_k:V_k\to Y$. A point $w\in V_k$ is a finite-valued minimizer of $({\cal P}_k)$ if and only if $f_2(A_kw)<+\infty$ and, for every $u\in V_k$,
--   $$
--   f_2(A_kw)+\langle b,u-w\rangle-(A_kw,A_k(u-w))\le f_2(A_ku).
--   $$
--   This is the variational inequality (4.4), rearranged so no subtraction of infinite values is needed. It characterizes discrete solutions for the later estimates.
--
--   **Formalization Note** The printed inequality subtracts $f_2(A_kw)$; the equivalent rearrangement is well-defined in `EReal` and requires its displayed finite-value condition.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 21, (4.4)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (4.4), with the extended-real difference rearranged. -/
theorem eq_4_4 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (k : ℕ) (w : Vh k) :
    IsSolutionH (Ah k) f₂ b w ↔ f₂ (Ah k w) ≠ ⊤ ∧ ∀ u : Vh k,
      f₂ (Ah k w) + ((b (u - w) - inner ℝ (Ah k w) (Ah k (u - w)) : ℝ) : EReal) ≤
        f₂ (Ah k u) := by sorry

end GabayMercier.Approximation
