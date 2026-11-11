-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_C_1
-- name    : GrothendieckPD.Digits.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:49.943953+00:00
-- url     : https://prove2.me/theorems/6dbc798a-9783-47d5-8fe8-418dc8e62010
-- title:
--   Lemma C.1: $c_1-\sum_{m=2}^{681}|c_m|>0.5618773799453352$
-- statement:
--   For the rounding scheme $\mu=\sum_{i=0}^{31}\lambda_i\delta_{(f_i,g_i)}$ of §4.2 with $H=H_\mu=\sum_i\lambda_iH_i$ and $c_m=[t^m]H$,
--   $$c_1-\sum_{m=2}^{681}|c_m|>0.5618773799453352.\qquad(C.5)$$
--
--   This is the head estimate of the upper-bound certificate.
--
--   Differences from the source:
--   - encoding: [t^m] H_i, the Taylor coefficient of H_i = H_{f_i, g_i} → c_m(f_i, g_i) = ∑_{gr(α) = m} f̂_α ĝ_α (gradedInner); reason: the source defines the coefficients this way ('by definition (3.3)', p. 14)
--   - encoding: sign(·) in F, F_* and sign W → sign(0) = 1; reason: the value at 0 is taken on a null set; this is the convention of the proof of Lemma 3.3 (p. 8)
--   - encoding: round each root to the nearest multiple of 10⁻¹² → round(r·10¹²)/10¹² with Mathlib's round (ties upward); reason: the source states that the rounding is unique (p. 47), so the tie rule is never used
--   - encoding: k/256 ≤ y < (k+1)/256, 0 ≤ k < 2048 → k = ⌊256 y⌋ for 0 ≤ y < 8; reason: the same strip
--   - encoding: variables X_i^{(d)}, grade d ≥ 1, i = 1, 2, … → coordinates of ℕ+ × ℕ → ℝ under the product of standard Gaussians; X_i^{(d)} is coordinate (d, i), the index i = 0 being an extra unused variable of each grade; reason: countably many i.i.d. N(0,1) variables of each grade, as on pp. 7–8
--   - encoding: decimal constants → exact rationals; reason: the source says every decimal is exact
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma C.1, Eq. (C.5), p. 24

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme

namespace GrothendieckPD.Digits

/-- Lemma C.1 (p. 24), Eq. (C.5): the coefficients of `H = H_µ` for the rounding scheme of §4.2
satisfy `c_1 - ∑_{m=2}^{681} |c_m| > 0.5618773799453352`. -/
theorem lemma_C_1 :
    (0.5618773799453352 : ℝ) < cMix 1 - ∑ m ∈ Finset.Icc 2 681, |cMix m| := by sorry

end GrothendieckPD.Digits
