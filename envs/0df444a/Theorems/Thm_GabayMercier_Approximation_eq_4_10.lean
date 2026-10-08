-- Prove2me | Theorems.Thm_GabayMercier_Approximation_eq_4_10
-- name    : GabayMercier.Approximation.eq_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:37.222234+00:00
-- url     : https://prove2.me/theorems/1170fa47-dba3-4679-af9c-00b789e2970e
-- title:
--   Equation (4.10) — upper bound for the image discrepancy
-- statement:
--   Under the hypotheses of Theorem 4.1, let $v^*$ solve $({\cal P})$ and $v_k^*$ be any eventual discrete solutions. For every $v\in V$ with $f_2(Av)<+\infty$, put $X_k=\|A_kv_k^*-Av^*\|^2$. Then
--   $$
--   \limsup_{k\to\infty}X_k\le(Av^*,Av)+f_2(Av)-f_2(Av^*)-\langle b,v-v^*\rangle-\|Av^*\|^2.
--   $$
--   This is (4.10), the last estimate before selecting $v=v^*$.
--
--   **Formalization Note** Lean states the limsup bound through every positive error $\varepsilon$: the inequality with $+\varepsilon$ holds eventually. Both $f_2$ values converted to real numbers are finite; $f_2(Av^*)$ is finite because $v^*$ is a solution.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 22, (4.10)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (4.10), phrased as an eventual real bound with arbitrary positive error. -/
theorem eq_4_10 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k))
    (v : V) (hv : f₂ (A v) ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ‖Ah k (vh k) - A vs‖ ^ 2 ≤ inner ℝ (A vs) (A v) + (f₂ (A v)).toReal -
        (f₂ (A vs)).toReal - b (v - vs) - ‖A vs‖ ^ 2 + ε := by sorry

end GabayMercier.Approximation
