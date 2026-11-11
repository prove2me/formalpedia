-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_theorem_4_2
-- name    : GrothendieckPD.Digits.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:08:33.156606+00:00
-- url     : https://prove2.me/theorems/d9a72953-30f3-495f-9587-9d2fc08f327a
-- title:
--   Theorem 4.2: $c_1-\sum_{\mathrm{odd}\ m\ge3}|c_m|>0.561831528950464991>1000000/1779893$; $K_G<1.779893$
-- statement:
--   For the rounding scheme $\mu$ of §4.2 (Table 1, Eqs. 4.2–4.7 and the staircase data of p. 48), with $c_m=c_m(\mu)$,
--   $$c_1-\sum_{\substack{m\ge3\\ m\text{ odd}}}|c_m|>0.561831528950464991>\frac{1000000}{1779893}.$$
--   In particular, $K_G<1.779893$.
--
--   This is the upper half of the main theorem: an explicit Krivine rounding scheme on the graded Gaussian space.
--
--   Differences from the source:
--   - encoding: [t^m] H_i, the Taylor coefficient of H_i = H_{f_i, g_i} → c_m(f_i, g_i) = ∑_{gr(α) = m} f̂_α ĝ_α (gradedInner); reason: the source defines the coefficients this way ('by definition (3.3)', p. 14)
--   - encoding: sign(·) in F, F_* and sign W → sign(0) = 1; reason: the value at 0 is taken on a null set; this is the convention of the proof of Lemma 3.3 (p. 8)
--   - encoding: round each root to the nearest multiple of 10⁻¹² → round(r·10¹²)/10¹² with Mathlib's round (ties upward); reason: the source states that the rounding is unique (p. 47), so the tie rule is never used
--   - encoding: k/256 ≤ y < (k+1)/256, 0 ≤ k < 2048 → k = ⌊256 y⌋ for 0 ≤ y < 8; reason: the same strip
--   - encoding: variables X_i^{(d)}, grade d ≥ 1, i = 1, 2, … → coordinates of ℕ+ × ℕ → ℝ under the product of standard Gaussians; X_i^{(d)} is coordinate (d, i), the index i = 0 being an extra unused variable of each grade; reason: countably many i.i.d. N(0,1) variables of each grade, as on pp. 7–8
--   - encoding: decimal constants → exact rationals; reason: the source says every decimal is exact
--   - encoding: an infinite sum of absolute values of coefficients → the tsum together with the assertion that the series is summable; reason: Lean's tsum is 0 on a non-summable series; the source's series converge absolutely (Lemma 2.5 on the graded space, pp. 8 and 14), so the extra clause excludes only the undefined case
--   - encoding: K_G = sup_{m,n} sup_{A} SDP(A)/OPT(A) (Eq. 1.1) → K_G = inf{K : SDP(A) ≤ K·OPT(A) for all real matrices A} (published GrothendieckConstant.grothendieckConst), with unit vectors in ℝ^d for arbitrary d; reason: same value: the ratio is undefined only at A = 0, where both sides vanish; OPT(A) > 0 for A ≠ 0; the admissible set is nonempty (Grothendieck's inequality) and bounded below; unit vectors in any dimension give the same SDP value as in ℝ^{m+n}
--   - encoding: the sum over odd degrees m ≥ 3 → the sum over k : ℕ with m = 2*k + 3; reason: a bijective reindexing of every odd degree at least 3
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Theorem 4.2, p. 14

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme

namespace GrothendieckPD.Digits

/-- Theorem 4.2 (p. 14). For the rounding scheme of §4.2,
`c_1 - ∑_{m ≥ 3, m odd} |c_m| > 0.561831528950464991 > 1000000/1779893` (the odd-tail series
converging absolutely); in particular `K_G < 1.779893`. -/
theorem theorem_4_2 :
    (Summable fun k => |cMix (2 * k + 3)|) ∧
      (0.561831528950464991 : ℝ) < cMix 1 - ∑' k, |cMix (2 * k + 3)| ∧
      (1000000 / 1779893 : ℝ) < 0.561831528950464991 ∧
      GrothendieckConstant.grothendieckConst < 1779893 / 1000000 := by sorry

end GrothendieckPD.Digits
