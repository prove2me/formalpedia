-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_claim_5_2_1
-- name    : ITPIRPreproc.MatchVec.claim_5_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:19.999604+00:00
-- url     : https://prove2.me/theorems/3078ec9f-24df-45f3-ab79-1aa564fa5934
-- title:
--   Claim 5.2.1 — compatibility and overlap of the basic matching-vector keys; the sampler (9) is uniform on $\mathcal R_i$
-- statement:
--   Let $m=2^h$ with $h\ge3$, and let $u_a,v_a\in\mathbb Z_6^d$ ($a\in[m]$) satisfy (7) with the vectors $v_a\bmod2$ pairwise distinct. Consider the key space $\mathcal R=\mathbb F_2^{h\times d}$ with $S(R)=\{(a,Rv_a):a\in[m]\}$ and $\mathcal R_i=\{R: i\in S(R)\}$. For every pair of distinct positions $i=(a,b)$ and $j=(a',b')$ in $[m]\times\mathbb F_2^h$,
--   $$\Pr_{R\leftarrow\mathcal R}[i\in S(R)]=\frac1m,\qquad \Pr_{R\leftarrow\mathcal R_i}[j\in S(R)]\le\frac1m.$$
--   Moreover, if $R_0\leftarrow\mathcal R$ is uniform, the key $R_0+(b-R_0v_a)u_a^T$ of (9) is uniform on $\mathcal R_i$.
--
--   This gives property (i) of Definition 4.1 for the basic construction, and its sampler statement is reused for the matrix part of the activation-bit sampler (15) in Claim 6.2.1.
--
--   Differences from the source:
--   - encoding: probabilities over R ← R and R ← R_i; the sampler returns a uniform key from R_i → normalized counts (#R)⁻¹·#{…} and averages (#R_i)⁻¹·Σ_{R∈R_i}; the image law of the uniform R₀ under the sampler equals the uniform law on R_i; reason: uniform laws on finite sets; same probabilities
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 5.2.1, printed p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_BasicKeys
import Definitions.Def_ITPIRPreproc_MatchVec_OneCompatibleHint

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

/-- Claim 5.2.1, printed p.18 (PDF p.20). For a matching-vector family (7) with distinct
`v_a mod 2`, `m = 2^h`, the basic key space `R = F₂^{h×d}` and `S(R) = {(a, R v_a)}`: for distinct
positions `i, j`, `Pr_{R←R}[i ∈ S(R)] = 1/m` and `Pr_{R←R_i}[j ∈ S(R)] ≤ 1/m`; the sampler (9)
maps the uniform law on `R` to the uniform law on `R_i`. -/
theorem claim_5_2_1 (h d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) (hh : 3 ≤ h)
    (hmv : IsMVFamily (2 ^ h) d u v) :
    (∀ i j : Pos h, i ≠ j →
      (Fintype.card (BasicKey h d) : ℝ≥0∞)⁻¹ * (basicCompat v i).card = (2 ^ h : ℝ≥0∞)⁻¹ ∧
      avgOver (basicCompat v i) (fun R => if basicSel v R j then 1 else 0) ≤
        (2 ^ h : ℝ≥0∞)⁻¹) ∧
    ∀ (i : Pos h) (R : BasicKey h d),
      (Fintype.card (BasicKey h d) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun R₀ => basicSampler u v i R₀ = R).card =
        if basicSel v R i then ((basicCompat v i).card : ℝ≥0∞)⁻¹ else 0 := by sorry

end ITPIRPreproc.MatchVec
