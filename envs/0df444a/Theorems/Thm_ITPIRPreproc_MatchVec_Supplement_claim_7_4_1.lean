-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_Supplement_claim_7_4_1
-- name    : ITPIRPreproc.MatchVec.Supplement.claim_7_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:59.838487+00:00
-- url     : https://prove2.me/theorems/a7ba9485-1da0-4db6-9ee4-d9ebc98d35e7
-- title:
--   Claim 7.4.1 — compatibility $1/m$ and overlap $2/m$ of the majority keys; the conditional sampler is uniform on $\mathcal R_i$
-- statement:
--   Let $m=2^h$ with $h\ge3$. Fix an integer $H\ge h+64$, with $d=2H^{14}+1$ and $\mu=H^{-6}$. Consider the key space $\mathcal R=\{-1,+1\}^{h\times d}$ with $S(R)=\{(a,\operatorname{sgn}(Rv_a)):a\in[m]\}$, where the $v_a$ are the row vectors of a seed, and let $\mathcal R_i=\{R:i\in S(R)\}$. Then:
--
--   1. for every seed and every position $i=(a,b)\in[m]\times\{-1,+1\}^h$,
--   $$\Pr_{R\leftarrow\mathcal R}[i\in S(R)]=\frac1m;$$
--   2. for every good seed and every pair of distinct positions $i,j$,
--   $$\Pr_{R\leftarrow\mathcal R_i}[j\in S(R)]\le\frac2m;$$
--   3. for every seed and position $i=(a^\star,b^\star)$, the conditional sampler returns a uniform key from $\mathcal R_i$. The sampler negates each uniform block $r_t$ whose majority sign $\operatorname{sgn}\langle r_t,v_{a^\star}\rangle$ differs from $b^\star_t$.
--
--   This is property (i) of Definition 4.1 for the majority primitive, together with the exact conditional sampler used by the compiler.
--
--   **Formalization Note** $\Pr_{R\leftarrow\mathcal R}$ is $|\mathcal R_i|/|\mathcal R|$. $\Pr_{R\leftarrow\mathcal R_i}$ is the average over $\mathcal R_i$ (`avgOver`). The sampler statement says that the image of the uniform law on $\mathcal R$ under the sampler is the uniform law on $\mathcal R_i$.
--
--   Differences from the source:
--   - encoding: probabilities over R ← R and R ← R_i; the sampler returns a uniform key from R_i → normalized counts (#R)⁻¹·#R_i and averages over R_i; the image of the uniform law on R under the sampler equals the uniform law on R_i; reason: uniform laws on finite sets; same probabilities
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 7.4.1, printed p.28 (PDF p.30); objects Eq. (22) and Key sampling, printed p.26 (PDF p.28)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Supplement_Majority

open scoped ENNReal

namespace ITPIRPreproc.MatchVec.Supplement

/-- Claim 7.4.1, printed p.28 (PDF p.30). Under the §7.2 parameters (`m = 2^h`, `h ≥ 3`, integer
`H ≥ h + 64`, `d = 2H^14 + 1`, `µ = H^{−6}`), with key space `R = {−1,+1}^{h×d}` and
`S(R) = {(a, sgn(R v_a))}`:
(1) for every seed and every position `i`, `Pr_{R←R}[i ∈ S(R)] = 1/m`;
(2) for every good seed and distinct positions `i, j`, `Pr_{R←R_i}[j ∈ S(R)] ≤ 2/m`;
(3) for every seed and position `i`, the conditional sampler maps the uniform law on `R` to the
uniform law on `R_i`. -/
theorem claim_7_4_1 (h H : ℕ) (hh : 3 ≤ h) (hH : h + 64 ≤ H) :
    (∀ (σ : Seed h H) (i : MPos h),
      (Fintype.card (Key h H) : ℝ≥0∞)⁻¹ * (majCompat σ i).card = ((2 : ℝ≥0∞) ^ h)⁻¹) ∧
    (∀ σ : Seed h H, IsGood σ → ∀ i j : MPos h, i ≠ j →
      avgOver (majCompat σ i) (fun R => if majSel σ R j then 1 else 0) ≤ 2 / (2 : ℝ≥0∞) ^ h) ∧
    (∀ (σ : Seed h H) (i : MPos h) (R : Key h H),
      (Fintype.card (Key h H) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun R₀ => majSampler σ i R₀ = R).card =
        if majSel σ R i then ((majCompat σ i).card : ℝ≥0∞)⁻¹ else 0) := by sorry

end ITPIRPreproc.MatchVec.Supplement
