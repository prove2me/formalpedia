-- Prove2me | Theorems.Thm_GOLiQ_corollary_3
-- name    : GOLiQ.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:02.107201+00:00
-- url     : https://prove2.me/theorems/12ebf710-e96c-43bf-927a-2a4d2cd63c9a
-- title:
--   Corollary 3 — $|I_3|=O(k^{-\alpha})$
-- statement:
--   Under the conditions of Theorem 1 (see Corollary 1),
--   $$|I_3|=O(k^{-\alpha}),\qquad I_3=\mathbb E\Big[(D_k-\lambda_kT_k)\Big(h_0w(\mu_k,p_k)+\frac{h_0}{\mu_k}-p_k\Big)\Big]+\mathbb E\Big[\sum_{n=1}^{Q_k\wedge D_k}(p_k-p^k_n)\Big],$$
--   with $\lambda_k=\lambda(p_k)$ and $T_k$ the length of cycle $k$.
--
--   $I_3$ collects the cost of the mismatch between the number of customers served and the steady-state rate, and of the old fees charged to leftover customers.
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
--   - reading: O(k^{−α}) → a constant K′ > 0 chosen after the policy with |I₃| ≤ K′k^{−α} for all k ≥ 1; reason: the paper's O-notation
--   - generalization: |I₃| = O(k^{−α}) → also asserts that Tₖ is integrable; reason: an added conclusion implied by Lemma 1; it excludes the junk value 0 of a non-integrable expectation in I₃
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Corollary 3, p.27; I₃, p.22

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

/-- **Corollary 3** (Chen, Liu, Hong, arXiv:2009.02911v3, p.27): under the conditions of Theorem 1,
`|I₃| = O(k^{−α})`, where (p.22)

`I₃ = E[(Dₖ − λₖTₖ)(h₀w(µₖ, pₖ) + h₀/µₖ − pₖ)] + E[Σ_{n=1}^{Qₖ∧Dₖ} (pₖ − pₙᵏ)]`.

**Formalization Note.** `O(k^{−α})` is a constant `K′ > 0` independent of `k ≥ 1`, chosen after the
policy. The conditions of Theorem 1 are as in Corollary 1. The statement also asserts
that the cycle length `Tₖ` is integrable, so that `I₃` is a genuine expectation. -/
theorem corollary_3 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η θ a γ : ℝ, Assumption2 M Pr η θ a γ → η ≤ η₀ →
    ∀ K₂ α : ℝ, 0 < K₂ → 0 < α → α ≤ 1 →
    ∀ D : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → 1 ≤ D k) →
      (∀ k : ℕ, 1 ≤ k →
        ⌈6 * Real.log k / min γ η⌉₊ ≤ D k ∧ (D k : ℝ) ≤ K₂ * (k : ℝ) ^ (2 - α)) →
    ∀ x : ℕ → Ω → Point, M.Admissible Pr D x →
      (∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ‖x k ω - x (k + 1) ω‖ₑ ^ 2 ∂Pr.P ≤ ENNReal.ofReal (K₂ * (k : ℝ) ^ (-2 * α))) →
      ∃ K' : ℝ, 0 < K' ∧ ∀ k : ℕ, 1 ≤ k →
        Integrable (fun ω => (M.system Pr D x ω).length k) Pr.P ∧
        |M.nonstatRemainder Pr D x k| ≤ K' * (k : ℝ) ^ (-α) := by sorry

end GOLiQ
