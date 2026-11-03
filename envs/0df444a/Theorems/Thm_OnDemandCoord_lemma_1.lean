-- Prove2me | Theorems.Thm_OnDemandCoord_lemma_1
-- name    : OnDemandCoord.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:16.960282+00:00
-- url     : https://prove2.me/theorems/9ca037ac-deb2-4c42-b888-37cee49d167b
-- title:
--   Lemma 1 (fill rates as $T\to\infty$): TFRB with optimal target fill rates attains the minimum staffing cost
-- statement:
--   **Lemma 1** (p. 15). Let $(Q^*,\eta^*)$ be a system optimum, $S^*=NG(\eta^*)$, and $\beta^*$ an optimal solution of the linear program (8) at $(Q^*,S^*)$. For any run data:
--   1. for every $T\ge2$, with the TFRB policy $\kappa_T$ (target fill rates $\beta^*$), the total staffing cost of p. 11,
--   $$p\sum_i\mathbb E\big[(X_i-Q^*_i)^+-A_i\big]+\eta^*NG(\eta^*)+c\sum_iQ^*_i,$$
--   equals $C(Q^*,\eta^*)$, and it is at most the total cost of every $(Q,\eta,\kappa)$ with $Q\ge0$ and $\kappa\in\mathcal A$: the system achieves the minimum staffing cost;
--   2. for every firm $i$, $$\lim_{T\to\infty}\mathbb E\big[A_i((X-Q^*)^+,S^*)\big]=\beta^*_i\,\mathbb E[(X_i-Q^*_i)^+].$$
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - reading: E[A*_i] = β*_i E[(X_i − Q_i*)⁺] for the TFRB policy at a 'large' T → the limit as T → ∞; reason: an exact equality at finite T fails in the generality of §A.4.3 (n = 2, X_i ~ U(1,2), S = 1: E[A_1] has denominator T − 1, β*_1E[X̂_1] = 1/√2; paper.md item 3)
--   - generalization: T a large number → the cost clause at every T ≥ 2; reason: the no-waste property holds at every T
--   - reading: Q*, η* as described in Theorem 1 → any global minimizer of (5); reason: p. 10 defines the system optimum as the minimizer; Theorem 1's formulas need extra hypotheses (paper.md items 2, 4)
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Lemma 1 and (8), p. 15; proof §A.4, pp. A3–A7 (PDF 35–39)

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Lemma 1, with the fill rates as a limit**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 15. Let `(Q*, η*)` be a system optimum
and `β*` optimal for (8). For every `T ≥ 2`, the TFRB policy at `(Q*, η*)` attains the minimum
staffing cost: the total cost of p. 11 equals `C(Q*, η*)`, and no `(Q, η, κ)` with `Q ≥ 0`,
`κ ∈ 𝒜` does better. Moreover, `E[A_i((X − Q*)⁺, S*)] → β_i* E[(X_i − Q_i*)⁺]` as `T → ∞`.

**Formalization Note.** The paper runs Algorithm 1 at "large" `T`, and its proof ends "for large enough
`T`". Equality at a finite `T` fails in the generality of §A.4.3, so "moreover" is the limit. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar)
    (β : Fin n → ℝ) (hβ : M.IsOptimalLP Qstar (M.S ηstar) β)
    (run : RunData n (M.S ηstar)) :
    (∀ T : ℕ, 2 ≤ T →
      M.origCost Qstar ηstar (M.tfrb Qstar (M.S ηstar) β run T) = M.C Qstar ηstar ∧
      ∀ (Q : Fin n → ℝ) (η : ℝ) (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)),
        0 ≤ Q → IsPolicy κ →
        M.origCost Qstar ηstar (M.tfrb Qstar (M.S ηstar) β run T) ≤ M.origCost Q η κ) ∧
    ∀ i, Tendsto (fun T : ℕ => M.expAlloc (M.tfrb Qstar (M.S ηstar) β run T) Qstar (M.S ηstar) i)
      atTop (𝓝 (β i * M.mean Qstar i)) := by sorry

end OnDemandCoord
