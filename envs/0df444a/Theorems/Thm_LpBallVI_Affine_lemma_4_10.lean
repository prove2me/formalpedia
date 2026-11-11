-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_10
-- name    : LpBallVI.Affine.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:12:54.242285+00:00
-- url     : https://prove2.me/theorems/73330e97-b98f-4362-a90c-9b93107dea30
-- title:
--   Lemma 4.10 — an integer radius R = O_p(n) and c_R > 0 force the multiplier λ = ‖F(z*)‖_q/R^{p−1} within κ of 1
-- statement:
--   Let $1 < p < \infty$, $p \ne 2$, $\eta = 1/128$, a coefficient family with all $a_{{\rm gate},j} > 0$, and $\kappa > 0$. There is a constant $C$ such that for every well-formed PureCircuit instance with $n \ge 2$ nodes there are an integer radius $1 \le R \le Cn$ and $c_R > 0$ with the following property for the operator $F$ of (39)–(40): every $z^* \in B_p(R)$ with
--   $$\|z^* - s\|_p \le \min\Big\{\frac12, \frac{\eta}{12H}\Big\},\quad s = S_R(F(z^*)),\qquad\text{satisfies}\qquad \Big|\frac{\|F(z^*)\|_q}{R^{p-1}} - 1\Big| \le \kappa.$$
--   The anchor coordinate pins the common multiplier near 1, where Lemma 4.6 applies.
--
--   Differences from the source:
--   - generalization: κ, the accuracy of Lemma 4.6 for η = 1/128 → every κ > 0; reason: the paper's κ is one value
--   - generalization: the coefficient family of Lemma 4.6 for ϕ̂_NOR, ϕ̂_PURIFY → any real coefficient family with a_{gate,j} > 0; reason: the proof uses only Lemma 4.4(i), 4.7, 4.9 and a > 0; the paper's family is an instance
--   - generalization: z* an ϵ_R-approximate VI solution (41) → any z* ∈ B_p(R); reason: the proof does not use (41); approximate solutions are points of the ball
--   - reading: R = O_p(n) → ∃ C (depending on p, the family and κ, not on the instance) with 1 ≤ R ≤ C·n for every instance with n ≥ 2; reason: the standard meaning of O_p(n) with the constants fixed before the instance
--   - encoding: coordinates z = (z_0, ζ) ∈ ℝ^{d_aux+1} → functions on Option (Fin n × Fin m × Fin 6), none = z_0; reason: relabelling of the 6mn + 1 coordinates
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 33, Lemma 4.10, (49)–(51); R from (50) on p. 34

import Mathlib
import Definitions.Def_LpBallVI_Affine_Construction

namespace LpBallVI.Affine

/-- **Lemma 4.10**, p. 33, with `η = 1/128`: for every `κ > 0` (in the paper, the accuracy of
Lemma 4.6 for `η`) and every coefficient family with `a_{gate,j} > 0`, there is a constant `C` such
that for every `PureCircuit` instance with `n ≥ 2` nodes there are an integer radius
`1 ≤ R ≤ C n` (`R = O_p(n)`) and `c_R > 0` such that every `z* ∈ B_p^{d_aux+1}(R)` with
`‖z* − s‖_p ≤ min{1/2, η/(12H)}` (`s = S_R(F(z*))`) has multiplier
`λ = ‖F(z*)‖_q / R^{p−1}` with `|λ − 1| ≤ κ`. -/
theorem lemma_4_10 (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (c : CoeffFamily)
    (haN : ∀ j, 0 < c.aN j) (haP : ∀ j, 0 < c.aP j) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ I : PCInst, I.WellFormed → 2 ≤ I.n →
      ∃ R : ℕ, 1 ≤ R ∧ (R : ℝ) ≤ C * I.n ∧ ∃ cR : ℝ, 0 < cR ∧
        ∀ z : Coord I.n c.m → ℝ, z ∈ ball p (R : ℝ) →
          lpNorm p (z - supportPt p (R : ℝ) (vecF p I c cR z)) ≤
              min (1 / 2) ((1 / 128) / (12 * c.H)) →
            |lpNorm (dualExp p) (vecF p I c cR z) / (R : ℝ) ^ (p - 1) - 1| ≤ κ := by sorry

end LpBallVI.Affine
