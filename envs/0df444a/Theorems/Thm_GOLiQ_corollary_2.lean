-- Prove2me | Theorems.Thm_GOLiQ_corollary_2
-- name    : GOLiQ.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:01.063212+00:00
-- url     : https://prove2.me/theorems/7c3aa55f-a899-4eff-9582-108f137909f3
-- title:
--   Corollary 2 — $\mathbb E|W^k_n-w(\mu_k,p_k)|=O(k^{-\alpha})$, (14)
-- statement:
--   Under the conditions of Theorem 1 (see Corollary 1), for all $k\ge2$ and $1\le n\le D_k$,
--   $$\mathbb E\big[|W^k_n-w(\mu_k,p_k)|\big]=O(k^{-\alpha}),\tag{14}$$
--   where $w(\mu,p)=\mathbb E[W_\infty(\mu,p)]$. As a direct consequence, $|I_2|=O(k^{-\alpha}\log k)$, where $I_2=h_0\mathbb E\big[\sum_{n=1}^{\tilde d_k}(W^k_n-w(\mu_k,p_k))\big]$ and $\tilde d_k=\lceil 5\log k/\min(\gamma,\eta)\rceil$.
--
--   This bounds the transient error during the warm-up period of each cycle.
--
--   Differences from the source:
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - encoding: x = (µ, p) with the Euclidean norm → a point of EuclideanSpace ℝ (Fin 2), coordinate 0 = µ, 1 = p; reason: the norm of p.12
--   - reading: a sufficiently small constant η > 0 (Assumption 2) → there is η₀ > 0, depending only on the model and the laws of U and V, such that the statement holds for every η ≤ η₀ that satisfies Assumption 2; reason: with η fixed the statement is false: U, V ~ Exp(1), λ(p̲) = 0.99, µ̲ = 1, µ̄ = 2, η = 0.5, θ = 0.005, a = 0.004, γ = 5·10⁻⁶ satisfy Assumption 2, yet under the constant policy (µ̲, p̲) E[exp(ηWₙ)] → E[exp(ηW∞)] = ∞; the proof of Lemma 1 (p.54) needs η below the decay rate η̄ of the dominating queue
--   - reading: the per-cycle indexing of §3.3 with leftovers, recursions (6)–(7) and the price rule of p.15 → one global customer index j = N_{k−1} + n; customer 0 arrives at time 0 to an empty system; customer j pays p_{c(j−1)}, c(i) the last cycle that started strictly before the arrival of customer i; reason: it reproduces (6)–(7) with W₀¹ = 0, Q₁ = 0, and charges the first new arrival of cycle k the old fee p_{k−1}
--   - reading: 𝓕ₖ, the σ-algebra including all events in the first k − 1 iterations → 𝓕ₖ = σ(Uⱼ, Vⱼ : j ≤ N_{k−1}; Z₁, …, Z_{k−1}); an admissible policy has each xₖ ∈ B and 𝓕ₖ-measurable; reason: the primitives of every customer who entered service in cycles 1, …, k − 1 and the coordinate draws (p.68: xₖ ∈ 𝓕ₖ)
--   - encoding: cycle lengths Dₖ → deterministic Dₖ ≥ 1; reason: a cycle serves at least one customer (Lemma 1 assumes Dₖ ≥ 1)
--   - encoding: W∞(µ, p), the steady-state waiting time → Loynes' supremum sup_{n≥0} Σ_{j=1}^n (Vⱼ/µ − Uⱼ/λ(p)) on the primitives; reason: it has the stationary law; it is the coupling from the past of p.58
--   - reading: O(k^{−α}) and O(k^{−α} log k) → one constant K′ > 0, chosen after the policy, uniform in k ≥ 2 and n; reason: the paper's O-notation
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Corollary 2, p.27; I₂, p.22

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Assumption2
import Definitions.Def_GOLiQ_lindley
import Definitions.Def_GOLiQ_loynesWait
import Definitions.Def_GOLiQ_Model_objective
import Definitions.Def_GOLiQ_CycleSystem
import Definitions.Def_GOLiQ_Primitives_info
import Definitions.Def_GOLiQ_Model_Admissible
import Definitions.Def_GOLiQ_Model_MomentBound
import Definitions.Def_GOLiQ_Model_regret

open MeasureTheory ProbabilityTheory

namespace GOLiQ

/-- **Corollary 2** (Chen, Liu, Hong, arXiv:2009.02911v3, p.27): under the conditions of Theorem 1,
for all `k ≥ 2` and `1 ≤ n ≤ Dₖ`,

`E[|Wₙᵏ − w(µₖ, pₖ)|] = O(k^{−α})`,    (14)

where `w(µ, p) = E[W∞(µ, p)]`. As a direct consequence, `|I₂| = O(k^{−α} log(k))`.

**Formalization Note.** `O(·)` is a constant `K′ > 0` independent of `k` and `n`, chosen after the
policy. The conditions of Theorem 1 are as in Corollary 1. `I₂ = h₀E[Σ_{n=1}^{d̃ₖ}(Wₙᵏ − w(µₖ, pₖ))]`
with `d̃ₖ = ⌈5 log(k)/min(γ, η)⌉` (p.22). -/
theorem corollary_2 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η θ a γ : ℝ, Assumption2 M Pr η θ a γ → η ≤ η₀ →
    ∀ K₂ α : ℝ, 0 < K₂ → 0 < α → α ≤ 1 →
    ∀ D : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → 1 ≤ D k) →
      (∀ k : ℕ, 1 ≤ k →
        ⌈6 * Real.log k / min γ η⌉₊ ≤ D k ∧ (D k : ℝ) ≤ K₂ * (k : ℝ) ^ (2 - α)) →
    ∀ x : ℕ → Ω → Point, M.Admissible Pr D x →
      (∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ‖x k ω - x (k + 1) ω‖ₑ ^ 2 ∂Pr.P ≤ ENNReal.ofReal (K₂ * (k : ℝ) ^ (-2 * α))) →
      ∃ K' : ℝ, 0 < K' ∧
        (∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, 1 ≤ n → n ≤ D k →
          ∫⁻ ω, ENNReal.ofReal |(M.system Pr D x ω).cycleWait k n -
              M.waitMean Pr (x k ω 0) (x k ω 1)| ∂Pr.P ≤
            ENNReal.ofReal (K' * (k : ℝ) ^ (-α))) ∧
        ∀ k : ℕ, 2 ≤ k →
          |M.h0 * ∫ ω, ∑ n ∈ Finset.Icc 1 ⌈5 * Real.log k / min γ η⌉₊,
              ((M.system Pr D x ω).cycleWait k n - M.waitMean Pr (x k ω 0) (x k ω 1)) ∂Pr.P| ≤
            K' * (k : ℝ) ^ (-α) * Real.log k := by sorry

end GOLiQ
