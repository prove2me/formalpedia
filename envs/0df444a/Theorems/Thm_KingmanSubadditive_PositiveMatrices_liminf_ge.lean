-- Prove2me | Theorems.Thm_KingmanSubadditive_PositiveMatrices_liminf_ge
-- name    : KingmanSubadditive.PositiveMatrices.liminf_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:19.892626+00:00
-- url     : https://prove2.me/theorems/7a0f08b3-c717-4d6e-8ea6-242324d9b2c8
-- title:
--   (2.2.3), p. 892 — P{lim inf n⁻¹ log [X_n]_ij ≥ λ} = 1
-- statement:
--   Assume the hypotheses of Theorem 5, let $X_n=Y_1\cdots Y_n$, and let $\lambda$ be a real random variable with $n^{-1}\log[X_n]_{11}\to\lambda$ almost surely. Then for every pair of indices $(i,j)$,
--   $$P\Big\{\liminf_{n\to\infty} n^{-1}\log [X_n]_{ij}\ \ge\ \lambda\Big\}=1. \qquad(2.2.3)$$
--
--   This is the lower half of the passage from the diagonal entry to all entries in the proof of Theorem 5.
--
--   **Formalization Note.** The extended-real lim inf inequality is written as: almost surely, for every $\varepsilon>0$, eventually $n^{-1}\log[X_n]_{ij}\ge\lambda-\varepsilon$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 892, §2.2, proof of Theorem 5, (2.2.3)

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, (2.2.3), p. 892 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)): if `λ` is the almost-sure limit of `n⁻¹ log [X_n]₁₁`, then for every
`(i, j)`, `P{lim inf n⁻¹ log [X_n]_ij ≥ λ} = 1`.

**Formalization Note.** `λ` is any real random variable with `n⁻¹ log [X_n]₁₁ → λ` almost
surely (the limit of the preceding milestone). "lim inf aₙ ≥ λ" in the extended reals is
encoded without a real `liminf` (whose junk value on unbounded sequences would change the
claim) as: for every `ε > 0`, eventually `aₙ ≥ λ − ε`. -/
theorem liminf_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y)
    (lam : Ω → ℝ)
    (hlam : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω 0 0) / n) atTop (𝓝 (lam ω)))
    (i j : Fin k) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, lam ω - ε ≤ Real.log (X Y n ω i j) / n := by sorry

end KingmanSubadditive.PositiveMatrices
