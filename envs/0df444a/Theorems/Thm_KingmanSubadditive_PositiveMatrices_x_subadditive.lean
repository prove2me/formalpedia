-- Prove2me | Theorems.Thm_KingmanSubadditive_PositiveMatrices_x_subadditive
-- name    : KingmanSubadditive.PositiveMatrices.x_subadditive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:23.309007+00:00
-- url     : https://prove2.me/theorems/5a26eec6-2c2f-402d-87d1-7346a70df5c6
-- title:
--   Proof of Theorem 5, p. 891 — x_st = −log [Y_{s+1}⋯Y_t]₁₁ satisfies S₁ and S₂ and has finite expectation g_{t−s}
-- statement:
--   Assume the hypotheses of Theorem 5: $Y_1,Y_2,\dots$ are random $k\times k$ matrices with strictly positive entries, $E|\log [Y_n]_{ij}|<\infty$ for all $n,i,j$, and $(Y_n)$ is stationary. Put
--   $$z_{st}=[Y_{s+1}Y_{s+2}\cdots Y_t]_{11},\qquad x_{st}=-\log z_{st}\qquad(s<t).$$
--   Then
--   1. each $x_{st}$ is a random variable;
--   2. (S₁) $x_{su}\le x_{st}+x_{tu}$ whenever $s<t<u$;
--   3. (S₂) the joint distributions of $(x_{s+1,t+1})$ coincide with those of $(x_{st})$;
--   4. each $x_{st}$ has finite expectation, equal to $g_{t-s}=E(x_{0,t-s})$.
--
--   Together with S₃ this makes $x$ a subadditive process in the sense of §1.1.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 891, §2.2, proof of Theorem 5

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, p. 891 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)), unnumbered: under the hypotheses of Theorem 5, `x_st = −log z_st` with
`z_st = [Y_{s+1} ⋯ Y_t]₁₁` satisfies S₁; since `(Y_n)` is stationary, S₂ holds; and each
`x_st` (`s < t`) is a random variable with finite expectation `g_{t−s}`.

**Formalization Note.** S₁ is pointwise (every outcome), S₂ is equality of the joint laws of
the two-parameter paths `(x_{s+1,t+1})` and `(x_st)` over pairs `s < t`. "Finite expectation
`g_{t−s}`" is integrability of `x_st` together with `E(x_st) = E(x_{0,t−s})`. -/
theorem x_subadditive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    (∀ s t : ℕ, s < t → Measurable (x Y s t)) ∧ KingmanSubadditive.Ergodic.S1 (x Y) ∧ KingmanSubadditive.Ergodic.S2 P (x Y) ∧
    (∀ s t : ℕ, s < t → Integrable (x Y s t) P ∧ ∫ ω, x Y s t ω ∂P = g P (x Y) (t - s)) := by sorry

end KingmanSubadditive.PositiveMatrices
