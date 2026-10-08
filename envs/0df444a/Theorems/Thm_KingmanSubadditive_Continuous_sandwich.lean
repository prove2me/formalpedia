-- Prove2me | Theorems.Thm_KingmanSubadditive_Continuous_sandwich
-- name    : KingmanSubadditive.Continuous.sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:45:38.231779+00:00
-- url     : https://prove2.me/theorems/3bf1f32d-dfb4-4156-bbbf-489b496ef130
-- title:
--   Proof of Theorem 4 — bound between consecutive integer times
-- statement:
--   Let $x$ be a continuous-parameter subadditive process. For an integer $n\ge1$, a real time $n<t<n+1$, and a sample point at which $\Omega_{[n,n+1]}$ is finite,
--
--   $$
--   x_{0,n+1}-\Omega_{[n,n+1]}\le x_{0t}\le x_{0n}+\Omega_{[n,n+1]}.
--   $$
--
--   This bounds each intermediate time by the neighboring integer-time values and the oscillation on that unit interval.
--
--   **Formalization Note** The paper prints a strict upper sign in the second display, although the preceding subadditivity inequality gives a non-strict sign. The statement uses $\le$. The restriction $n<t<n+1$ ensures every indexed variable in the intermediate inequalities has a valid pair of times.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 889, §1.4, proof of Theorem 4, sandwich display after (1.4.8)

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory

/-- Kingman, §1.4, proof of Theorem 4, p. 889, the sandwich display.
Formalization Note: `n ≥ 1` and `n < t < n+1` keep every coordinate valid;
finite oscillation at this sample point allows conversion from `ENNReal`
to real. The printed strict upper sign is corrected to `≤`. -/
theorem sandwich {S : Type*} [MeasurableSpace S]
    (P : Measure S) (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hnt : (n : ℝ) < t) (htn : t < (n : ℝ) + 1)
    (ω : S)
    (hfinite : oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω < ⊤) :
    x 0 ((n : ℝ) + 1) ω -
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal ≤
      x 0 t ω ∧
      x 0 t ω ≤ x 0 n ω +
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal := by sorry

end KingmanSubadditive.Continuous
