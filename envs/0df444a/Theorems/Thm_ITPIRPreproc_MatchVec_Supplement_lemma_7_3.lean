-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_Supplement_lemma_7_3
-- name    : ITPIRPreproc.MatchVec.Supplement.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:30.09454+00:00
-- url     : https://prove2.me/theorems/680023a9-5356-409a-8a39-414f013c3fd1
-- title:
--   Lemma 7.3 — a uniformly random seed is good except with probability $2m^2e^{-\mu^2d/2}\le 2e^{2h\ln2-H^2}$
-- statement:
--   Let $m=2^h$ with $h\ge3$. Fix an integer $H\ge h+64$, and set $d=2H^{14}+1$ and $\mu=H^{-6}$. A seed $\sigma=((g_k,\tau_k))_{k\in[d]}\in(\mathbb F_2^h\times\mathbb F_2)^d$ defines the row vectors $v_{a,k}=(-1)^{\langle a,g_k\rangle_2+\tau_k}$, $a\in[m]$. It is **good** if $|\langle v_a,v_{a'}\rangle|\le\mu d$ for all $a\ne a'$. For a uniformly random seed (uniform over all $2^{(h+1)d}$ seeds),
--   $$\Pr[\sigma\text{ is not good}]\le 2m^2\exp\!\Bigl(-\frac{\mu^2d}{2}\Bigr)\le 2\exp\bigl(2h\ln2-H^2\bigr).$$
--
--   In the proof of Theorem 7.1, this gives the probability $2^{-\lambda-1}$ that the seed sampled during preprocessing is bad (Eq. (30)).
--
--   **Formalization Note** The probability is the number of non-good seeds divided by the number of seeds. Both inequalities are stated. $h\ge3$ and $H\ge h+64$ are the standing assumptions of §7.2.
--
--   Differences from the source:
--   - encoding: Pr over a uniformly random seed → the number of non-good seeds divided by the number 2^{(h+1)d} of seeds; rows a identified with their binary labels (bit t of a is coordinate t); reason: uniform law on a finite set; the §5.2 identification of [m] with F_2^h
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Lemma 7.3, printed p.26 (PDF p.28); parameters Eq. (19), (20), (21), printed pp.24, 26 (PDF pp.26, 28)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Supplement_Majority

namespace ITPIRPreproc.MatchVec.Supplement

/-- Lemma 7.3, printed p.26 (PDF p.28). With `m = 2^h`, `h ≥ 3`, an integer `H ≥ h + 64`,
`d = 2H^14 + 1` and `µ = H^{−6}`: a uniformly random seed (uniform over all `2^{(h+1)d}` seeds) is
good except with probability at most `2m² exp(−µ²d/2)`, and `2m² exp(−µ²d/2) ≤ 2 exp(2h ln 2 − H²)`. -/
theorem lemma_7_3 (h H : ℕ) (hh : 3 ≤ h) (hH : h + 64 ≤ H) :
    ((Finset.univ.filter fun σ : Seed h H => ¬ IsGood σ).card : ℝ) /
          (Fintype.card (Seed h H) : ℝ) ≤
        2 * ((2 : ℝ) ^ h) ^ 2 * Real.exp (-(mu H ^ 2 * (dim H : ℝ) / 2)) ∧
      2 * ((2 : ℝ) ^ h) ^ 2 * Real.exp (-(mu H ^ 2 * (dim H : ℝ) / 2)) ≤
        2 * Real.exp (2 * h * Real.log 2 - (H : ℝ) ^ 2) := by sorry

end ITPIRPreproc.MatchVec.Supplement
