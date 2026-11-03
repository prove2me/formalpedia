-- Prove2me | Theorems.Thm_OnDemandCoord_lemma_2
-- name    : OnDemandCoord.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:23.793145+00:00
-- url     : https://prove2.me/theorems/b2e4aafd-8629-4f3d-ab46-ffe85fdca5ea
-- title:
--   Lemma 2: the contract makes $\eta^*$ and the TFRB policy the platform's best response
-- statement:
--   **Lemma 2** (p. 20). Let $(Q^*,\eta^*)$ be a system optimum, $S^*=NG(\eta^*)$, and $\beta^*$ an optimal solution of (8) at $(Q^*,S^*)$ with all $\beta^*_i>0$. Take the contract with these target fill rates and any $m_i$, $r_i$. For any run data:
--   1. for every $T\ge2$, the TFRB policy $\kappa_T$ is in $\mathcal A$, and for every $\eta'\in\mathbb R$ and every $\kappa'\in\mathcal A$, $$\Pi(\eta',\kappa'\mid Q^*)\le\Pi(\eta^*,\kappa_T\mid Q^*);$$
--   2. the target fill rates are warranted in expectation: $\lim_{T\to\infty}\mathbb E[A_i((X-Q^*)^+,S^*)]=\beta^*_i\,\mathbb E[(X_i-Q^*_i)^+]$ for every $i$.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - reading: fill rates 'warranted in expectation' with the TFRB policy → the limit as T → ∞ of the expected allocation; reason: as in Lemma 1 (paper.md item 3)
--   - generalization: T a large number → the best-response clause at every T ≥ 2; reason: it uses only the no-waste property
--   - encoding: w_i^F and w_i^C divide by β*_i → β*_i > 0 for every i; reason: (11)–(12) are undefined at β*_i = 0; such β* exist (Theorem 2)
--   - reading: Q* as in Theorem 1 → any global minimizer of (5); reason: p. 10's definition of the system optimum
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Lemma 2, p. 20; §5.2.1, pp. 19–20

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Lemma 2**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 20. With permanent staffing fixed at a system optimum `Q*`, the contract
(11)–(12), for positive optimal target fill rates and any `m`, `r`, makes `(η*, κ_T)` a best
response of the platform among all compensation rates and all policies in `𝒜`, for every `T ≥ 2`.
The target fill rates are warranted in expectation in the limit `T → ∞`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar)
    (K : Contract n) (hβ : M.IsOptimalLP Qstar (M.S ηstar) K.β) (hpos : ∀ i, 0 < K.β i)
    (run : RunData n (M.S ηstar)) :
    (∀ T : ℕ, 2 ≤ T →
      IsPolicy (M.tfrb Qstar (M.S ηstar) K.β run T) ∧
      ∀ (η' : ℝ) (κ' : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)), IsPolicy κ' →
        M.platformProfit K η' κ' Qstar ≤
          M.platformProfit K ηstar (M.tfrb Qstar (M.S ηstar) K.β run T) Qstar) ∧
    ∀ i, Tendsto
      (fun T : ℕ => M.expAlloc (M.tfrb Qstar (M.S ηstar) K.β run T) Qstar (M.S ηstar) i)
      atTop (𝓝 (K.β i * M.mean Qstar i)) := by sorry

end OnDemandCoord
