-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_C_4
-- name    : GrothendieckPD.Digits.lemma_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:40.468209+00:00
-- url     : https://prove2.me/theorems/be7f9c7e-5b34-4fa2-877f-f40343fb17f2
-- title:
--   Lemma C.4: tail bound above degree 681 for $\sum_{i\in\{0,15,16\}}\lambda_iH_i$
-- statement:
--   For the rounding scheme of §4.2,
--   $$\sum_{m>681}\Bigl|[t^m]\sum_{i\in\{0,15,16\}}\lambda_iH_i(t)\Bigr|<0.000007875733380418.\qquad(C.40)$$
--
--   One of three tail estimates combined in Theorem 4.2; it concerns the components carrying over 96% of the mass.
--
--   Differences from the source:
--   - encoding: [t^m] H_i, the Taylor coefficient of H_i = H_{f_i, g_i} → c_m(f_i, g_i) = ∑_{gr(α) = m} f̂_α ĝ_α (gradedInner); reason: the source defines the coefficients this way ('by definition (3.3)', p. 14)
--   - encoding: sign(·) in F, F_* and sign W → sign(0) = 1; reason: the value at 0 is taken on a null set; this is the convention of the proof of Lemma 3.3 (p. 8)
--   - encoding: round each root to the nearest multiple of 10⁻¹² → round(r·10¹²)/10¹² with Mathlib's round (ties upward); reason: the source states that the rounding is unique (p. 47), so the tie rule is never used
--   - encoding: k/256 ≤ y < (k+1)/256, 0 ≤ k < 2048 → k = ⌊256 y⌋ for 0 ≤ y < 8; reason: the same strip
--   - encoding: variables X_i^{(d)}, grade d ≥ 1, i = 1, 2, … → coordinates of ℕ+ × ℕ → ℝ under the product of standard Gaussians; X_i^{(d)} is coordinate (d, i), the index i = 0 being an extra unused variable of each grade; reason: countably many i.i.d. N(0,1) variables of each grade, as on pp. 7–8
--   - encoding: decimal constants → exact rationals; reason: the source says every decimal is exact
--   - encoding: an infinite sum of absolute values of coefficients → the tsum together with the assertion that the series is summable; reason: Lean's tsum is 0 on a non-summable series; the source's series converge absolutely (Lemma 2.5 on the graded space, pp. 8 and 14), so the extra clause excludes only the undefined case
--   - encoding: the tail sum over integer degrees m > 681 → the sum over k : ℕ with m = k + 682; reason: a bijective reindexing of the full infinite tail
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma C.4, Eq. (C.40), p. 37

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme

namespace GrothendieckPD.Digits

/-- Lemma C.4 (p. 37), Eq. (C.40):
`∑_{m>681} |[t^m] ∑_{i ∈ {0,15,16}} λ_i H_i(t)| < 0.000007875733380418`; the tail series converges. -/
theorem lemma_C_4 :
    (Summable fun k => |∑ i ∈ ({0, 15, 16} : Finset ℕ), lam i * Hcoef i (k + 682)|) ∧
      ∑' k, |∑ i ∈ ({0, 15, 16} : Finset ℕ), lam i * Hcoef i (k + 682)| <
        (0.000007875733380418 : ℝ) := by sorry

end GrothendieckPD.Digits
