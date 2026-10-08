-- Prove2me | Theorems.Thm_LeiBR_Rand_eqB3
-- name    : LeiBR.Rand.eqB3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:10:07.915554+00:00
-- url     : https://prove2.me/theorems/7a714954-955e-4ac5-871f-e7876924cc48
-- title:
--   (B.3) — $\mathbb E[\eta^{2\beta_{i,k}}] = (1 - p_i(1-\eta^2))^k \le \tilde\eta^{2k}$
-- statement:
--   Let player $i$'s coins $\chi_{i,0}, \chi_{i,1}, \dots$ be independent $\{0,1\}$-valued random variables with $\mathbb P(\chi_{i,k} = 1) = p_i \in (0,1]$, let $\beta_{i,k} = \sum_{l=0}^{k-1}\chi_{i,l}$ and $\eta \in (0,1)$. Then for every $k$,
--   $$\mathbb E\big[\eta^{2\beta_{i,k}}\big] = \big(1 - p_i(1 - \eta^2)\big)^k \le \big(1 - p_{\min}(1 - \eta^2)\big)^k = \tilde\eta^{2k}.$$
--
--   It bounds the second moment of the random inexactness $\alpha_{i,k} = \eta^{\beta_{i,k}+1}$, which enters the rate of Lemma 5.
--
--   **Formalization Note** The paper states the identity for $k \ge 1$; it also holds at $k = 0$, and the Lean statement covers every $k$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 32, App. B, (B.3)

import Mathlib
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- (B.3), App. B, p. 32. If player `i`'s coins `χ_{i,0}, χ_{i,1}, …` are independent Bernoulli(`p_i`)
variables and `β_{i,k} = ∑_{l<k} χ_{i,l}`, then
`E[η^{2β_{i,k}}] = (1 − p_i(1 − η²))^k ≤ (1 − p_min(1 − η²))^k = η̃^{2k}`. -/
theorem eqB3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (χ : Fin N → ℕ → Ω → ℕ) (hχ1 : ∀ i k ω, χ i k ω ≤ 1) (hχ_meas : ∀ i k, Measurable (χ i k))
    (hχ_prob : ∀ i k, P {ω | χ i k ω = 1} = ENNReal.ofReal (p i))
    (hχ_iid : ∀ i, iIndepFun (fun k => χ i k) P)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (i : Fin N) (k : ℕ) :
    ∫ ω, η ^ (2 * beta χ i k ω) ∂P = (1 - p i * (1 - η ^ 2)) ^ k ∧
    (1 - p i * (1 - η ^ 2)) ^ k ≤ (1 - pmin p * (1 - η ^ 2)) ^ k ∧
    (1 - pmin p * (1 - η ^ 2)) ^ k = etatil p η ^ (2 * k) := by sorry

end LeiBR.Rand
