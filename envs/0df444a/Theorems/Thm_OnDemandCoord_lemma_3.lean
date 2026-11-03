-- Prove2me | Theorems.Thm_OnDemandCoord_lemma_3
-- name    : OnDemandCoord.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:15.499438+00:00
-- url     : https://prove2.me/theorems/9c4c3887-06f5-4519-b63a-c5c3cd6c1969
-- title:
--   Lemma 3: with $m_i$ from (14), $Q^*_i$ is a dominant strategy for firm $i$
-- statement:
--   **Lemma 3** (p. 21). Let $(Q^*,\eta^*)$ be a system optimum and take the contract with
--   $$m_i=\frac{p\bar F_i(Q^*_i)-c}{p\bar F_i(Q^*_i)}\qquad(14)$$
--   and any fees $r_i$ and target fill rates $\beta_i>0$. Then for every firm $i$, all staffing levels $Q_{-i}\ge0$ of the other firms, every $\eta$ and every policy $\kappa\in\mathcal A$, the level $Q^*_i$ minimizes firm $i$'s cost $h_i(\,\cdot\mid Q_{-i},\kappa,\eta)$ over $Q_i\ge0$.
--
--   Each firm therefore chooses the system-wide optimal staffing level whatever the others do (p. 22: "$Q^*_i$ is a dominant strategy").
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - generalization: Q_i* is chosen given the platform's (η*, A*) and Q*_{−i} → Q_i* is a best response to every Q_{−i} ≥ 0, η and policy in 𝒜; reason: the dominance stated on p. 22; it specializes to the equilibrium condition
--   - generalization: under the standing assumption τ̲ < φ^p of §5 → no such assumption; reason: p F̄_i(Q_i*) ≥ c > 0 at every system optimum, so (14) is defined without it
--   - encoding: w_i^F and w_i^C divide by β*_i → β_i > 0 for every i; reason: (11)–(12) are undefined at β_i = 0
--   - reading: Q* as in Theorem 1 → any global minimizer of (5); reason: p. 10's definition of the system optimum
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Lemma 3 and (14), p. 21; p. 22

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **Lemma 3**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 21. Under the contract with `m_i` from (14), `Q_i*` minimizes firm `i`'s
cost over `q ≥ 0`, whatever the other firms' levels, the policy in `𝒜` and `η`: it is a dominant
strategy (p. 22).

**Formalization Note.** `Q*` is any system optimum. The standing assumption `τ̲ < φ^p` of §5 is not
needed: at every system optimum `p F̄_i(Q_i*) ≥ c > 0`, so (14) is well defined. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar)
    (K : Contract n) (hm : K.m = M.mParam Qstar) (hβ : ∀ i, 0 < K.β i)
    (i : Fin n) (Q : Fin n → ℝ) (hQ : 0 ≤ Q) (η : ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (hκ : IsPolicy κ) (q : ℝ) (hq : 0 ≤ q) :
    M.firmCost K i (Function.update Q i (Qstar i)) κ η ≤
      M.firmCost K i (Function.update Q i q) κ η := by sorry

end OnDemandCoord
