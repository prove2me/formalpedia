-- Prove2me | Theorems.Thm_OnDemandCoord_eq_13
-- name    : OnDemandCoord.eq_13
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:21:59.754337+00:00
-- url     : https://prove2.me/theorems/80dce76e-7118-481c-a537-e3db0176e429
-- title:
--   (13): firm $i$'s cost under the contract is $p(1-m_i)\mathbb E[(X_i-Q_i)^+]+cQ_i+r_i$
-- statement:
--   **(13)** (p. 21). Take a contract with fees $r_i$, parameters $m_i$ and target fill rates $\beta_i>0$, staffing levels $Q\ge0$, any $\eta$, and any policy $\kappa\in\mathcal A$. Then firm $i$'s expected staffing cost (3) is
--   $$h_i(Q_i\mid Q_{-i},\kappa,\eta)=p\,(1-m_i)\,\mathbb E[(X_i-Q_i)^+]+cQ_i+r_i .$$
--
--   It depends neither on the other firms' staffing levels nor on the platform's decisions: the contract removes the gaming among firms.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - generalization: under the proposed allocation (the TFRB policy) and η* → for every policy in 𝒜 and every η; reason: the reduction uses only A_i ≤ X̂_i; it specializes to the TFRB policy
--   - encoding: w_i^F and w_i^C divide by β*_i → β_i > 0 for every i; reason: (11)–(12) are undefined at β_i = 0
--   - reading: Q ranges over staffing levels Q_i ≥ 0 → hypothesis 0 ≤ Q; reason: the paper's domain of Q (problem (3), p. 9)
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), (13), p. 21

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **(13)**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 21. For any policy in `𝒜`, any `η`, `Q ≥ 0`, and positive target fill rates,
firm `i`'s cost (3) reduces to `h_i(Q_i) = p (1 − m_i) E[(X_i − Q_i)⁺] + c Q_i + r_i`. -/
theorem eq_13 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (K : Contract n) (hβ : ∀ i, 0 < K.β i) (i : Fin n) (Q : Fin n → ℝ) (hQ : 0 ≤ Q) (η : ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (hκ : IsPolicy κ) :
    M.firmCost K i Q κ η = M.p * (1 - K.m i) * M.mean Q i + M.c * Q i + K.r i := by sorry

end OnDemandCoord
