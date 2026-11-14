-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_1
-- name    : ITPIRPreproc.MatchVec.claim_6_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:20.234597+00:00
-- url     : https://prove2.me/theorems/6e0d54c8-f003-4a9a-a9ea-e6864f264491
-- title:
--   Claim 6.2.1 — compatibility and overlap with activation bits; the sampler (15) is uniform on $\mathcal R^+_i$
-- statement:
--   Let $m=2^h$ with $h\ge3$, and let $u_a,v_a\in\mathbb Z_6^d$ ($a\in[m]$) satisfy (7) with the vectors $v_a\bmod2$ pairwise distinct. Consider the key space $\mathcal R^+=\mathbb F_2^{h\times d}\times\mathbb F_2^d$ with $S(R,\rho)=\{(a,Rv_a): a\in[m],\ \langle\rho,v_a\rangle_2=1\}$ and $\mathcal R^+_i$ the keys compatible with $i$. For every pair of distinct positions $i=(a,b)$ and $j=(a',b')$ in $[m]\times\mathbb F_2^h$,
--   $$\Pr_{(R,\rho)\leftarrow\mathcal R^+}[i\in S(R,\rho)]=\frac1{2m},\qquad \Pr_{(R,\rho)\leftarrow\mathcal R^+_i}[j\in S(R,\rho)]\le\frac1{2m}.$$
--   Moreover, if $(R_0,\rho_0)\leftarrow\mathcal R^+$ is uniform, the output of the sampler (15) is uniform on $\mathcal R^+_i$.
--
--   This is property (i) of Definition 4.1 for the activation-bit primitive: the first inequality of (3) holds with equality, and the overlap probability $1/(2m)$ is below the required $2/m$.
--
--   Differences from the source:
--   - encoding: probabilities over R ← R and R ← R_i; the sampler returns a uniform key from R_i → normalized counts (#R)⁻¹·#{…} and averages (#R_i)⁻¹·Σ_{R∈R_i}; the image law of the uniform R₀ under the sampler equals the uniform law on R_i; reason: uniform laws on finite sets; same probabilities
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 6.2.1, printed p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

/-- Claim 6.2.1, printed p.22 (PDF p.24). For a matching-vector family (7) with distinct
`v_a mod 2`, `m = 2^h`, the key space `R⁺ = F₂^{h×d} × F₂^d` and the set (14): for distinct
positions `i, j`, `Pr_{(R,ρ)←R⁺}[i ∈ S(R, ρ)] = 1/(2m)` and `Pr_{(R,ρ)←R⁺_i}[j ∈ S(R, ρ)] ≤ 1/(2m)`;
the sampler (15) maps the uniform law on `R⁺` to the uniform law on `R⁺_i`. -/
theorem claim_6_2_1 (h d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) (hh : 3 ≤ h)
    (hmv : IsMVFamily (2 ^ h) d u v) :
    (∀ i j : Pos h, i ≠ j →
      (Fintype.card (ActKey h d) : ℝ≥0∞)⁻¹ * (actCompat v i).card = (2 * 2 ^ h : ℝ≥0∞)⁻¹ ∧
      avgOver (actCompat v i) (fun K => if actSel v K j then 1 else 0) ≤
        (2 * 2 ^ h : ℝ≥0∞)⁻¹) ∧
    ∀ (i : Pos h) (K : ActKey h d),
      (Fintype.card (ActKey h d) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun K₀ => actSampler u v i K₀ = K).card =
        if actSel v K i then ((actCompat v i).card : ℝ≥0∞)⁻¹ else 0 := by sorry

end ITPIRPreproc.MatchVec
