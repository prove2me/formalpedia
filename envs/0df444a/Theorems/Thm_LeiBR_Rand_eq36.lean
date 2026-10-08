-- Prove2me | Theorems.Thm_LeiBR_Rand_eq36
-- name    : LeiBR.Rand.eq36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:55.257238+00:00
-- url     : https://prove2.me/theorems/fac749a4-d884-47a0-ae33-04fd969e5961
-- title:
--   (36) — $\mathbb E[\eta^{-2\beta_{i,k}}] = (p_i(\eta^{-2}-1)+1)^k \le \tilde\eta_0^{-2k}$
-- statement:
--   Under the hypotheses of (B.3) (player $i$'s coins independent and Bernoulli($p_i$), $\beta_{i,k} = \sum_{l<k}\chi_{i,l}$, $\eta \in (0,1)$), for every $k$
--   $$\mathbb E\big[\eta^{-2\beta_{i,k}}\big] = \big(p_i(\eta^{-2} - 1) + 1\big)^k \le \big(p_{\max}(\eta^{-2} - 1) + 1\big)^k = \tilde\eta_0^{-2k}.$$
--
--   Since the number of SA steps at iteration $k$ is $j_{i,k} = \lceil Q_i/\eta^{2(\beta_{i,k}+1)}\rceil$, this identity controls the expected work per iteration in Theorem 2.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 16, §4.3, proof of Theorem 2, (36)

import Mathlib
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- (36), §4.3, proof of Theorem 2, p. 16. Under the hypotheses of (B.3),
`E[η^{−2β_{i,k}}] = (p_i(η^{−2} − 1) + 1)^k ≤ (p_max(η^{−2} − 1) + 1)^k = η̃₀^{−2k}`. -/
theorem eq36 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (χ : Fin N → ℕ → Ω → ℕ) (hχ1 : ∀ i k ω, χ i k ω ≤ 1) (hχ_meas : ∀ i k, Measurable (χ i k))
    (hχ_prob : ∀ i k, P {ω | χ i k ω = 1} = ENNReal.ofReal (p i))
    (hχ_iid : ∀ i, iIndepFun (fun k => χ i k) P)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (i : Fin N) (k : ℕ) :
    ∫ ω, (η ^ (2 * beta χ i k ω))⁻¹ ∂P = (p i * ((η ^ 2)⁻¹ - 1) + 1) ^ k ∧
    (p i * ((η ^ 2)⁻¹ - 1) + 1) ^ k ≤ (pmax p * ((η ^ 2)⁻¹ - 1) + 1) ^ k ∧
    (pmax p * ((η ^ 2)⁻¹ - 1) + 1) ^ k = (etatil0 p η ^ (2 * k))⁻¹ := by sorry

end LeiBR.Rand
