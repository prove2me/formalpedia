-- Prove2me | Theorems.Thm_GOLiQ_theorem_1
-- name    : GOLiQ.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:59.232417+00:00
-- url     : https://prove2.me/theorems/d0a87f64-2818-4234-af9f-4eb85c7625ce
-- title:
--   Theorem 1 — regret of nonstationarity $R_{1,k}\le Kk^{-\alpha}\log k$
-- statement:
--   Suppose Assumptions 1 and 2 hold. Let $(x_k)$ be an admissible policy and $D_k\ge1$ deterministic cycle lengths such that, for some $K_2>0$ and $0<\alpha\le1$,
--
--   1. $\lceil 6\log(k)/\min(\gamma,\eta)\rceil\le D_k\le K_2k^{2-\alpha}$;
--   2. $\mathbb E[\|x_k-x_{k+1}\|^2]\le K_2k^{-2\alpha}$.
--
--   Then there is a constant $K>0$ such that
--   $$R_{1,k}\le K\,k^{-\alpha}\log k,\quad k\ge2,\qquad\text{and}\qquad R_1(L)\le K\sum_{k=1}^Lk^{-\alpha}\log k,\quad L\ge2.\tag{12}$$
--
--   Here $R_{1,k}=\rho_k-\mathbb E[f(\mu_k,p_k)T_k]$ is the regret due to the queue not being in steady state after each policy change. The bound is sublinear, against the crude $O(L)$ bound.
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
--   - generalization: R₁,ₖ = ρₖ − E[f(µₖ, pₖ)Tₖ] → also asserts integrability of the cycle cost, of Tₖ and of f(µₖ, pₖ)Tₖ for every k ≥ 1; reason: an added conclusion implied by Lemma 1; it excludes the junk value 0 of a non-integrable expectation
--   - encoding: W∞(µ, p), the steady-state waiting time → Loynes' supremum sup_{n≥0} Σ_{j=1}^n (Vⱼ/µ − Uⱼ/λ(p)) on the primitives; reason: it has the stationary law; it is the coupling from the past of p.58
--   - encoding: f of (2), through the steady-state queue length Q∞(µ, p) → f defined by (5), h₀λ(p)(E[W∞(µ, p)] + 1/µ) + c(µ) − pλ(p); reason: the paper's own identity (5) (Little's law, p.13) for every (µ, p) ∈ B; Q∞ is not used elsewhere
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Theorem 1, p.21; (8)–(11), p.19

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

/-- **Theorem 1 (regret of nonstationarity)** (Chen, Liu, Hong, arXiv:2009.02911v3, p.21): suppose
Assumptions 1 and 2 hold, and for some `K₂ > 0` and `0 < α ≤ 1`

(a) `⌈6 log(k)/min(γ, η)⌉ ≤ Dₖ ≤ K₂k^{2−α}`;
(b) `E[‖xₖ − xₖ₊₁‖²] ≤ K₂k^{−2α}`.

Then there is `K > 0` such that

`R₁,ₖ ≤ K·k^{−α} log(k)`, `k ≥ 2`,  and  `R₁(L) ≤ K Σ_{k=1}^L k^{−α} log(k)`, `L ≥ 2`.    (12)

**Formalization Note.** `R₁,ₖ = ρₖ − E[f(µₖ, pₖ)Tₖ]` ((10), p.19). The policy is admissible (each
`xₖ ∈ B` is determined by the first `k − 1` iterations), `Dₖ ≥ 1` is deterministic and `η` is
sufficiently small (as in Lemma 1). The statement also asserts that the cycle cost of (8), `Tₖ` and
`f(µₖ, pₖ)Tₖ` are integrable, so that `R₁,ₖ` is a genuine difference of expectations. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η θ a γ : ℝ, Assumption2 M Pr η θ a γ → η ≤ η₀ →
    ∀ K₂ α : ℝ, 0 < K₂ → 0 < α → α ≤ 1 →
    ∀ D : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → 1 ≤ D k) →
      (∀ k : ℕ, 1 ≤ k →
        ⌈6 * Real.log k / min γ η⌉₊ ≤ D k ∧ (D k : ℝ) ≤ K₂ * (k : ℝ) ^ (2 - α)) →
    ∀ x : ℕ → Ω → Point, M.Admissible Pr D x →
      (∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ‖x k ω - x (k + 1) ω‖ₑ ^ 2 ∂Pr.P ≤ ENNReal.ofReal (K₂ * (k : ℝ) ^ (-2 * α))) →
      ∃ K : ℝ, 0 < K ∧
        (∀ k : ℕ, 1 ≤ k →
          Integrable (fun ω => (M.system Pr D x ω).cost k) Pr.P ∧
          Integrable (fun ω => (M.system Pr D x ω).length k) Pr.P ∧
          Integrable (fun ω => M.objective Pr (x k ω) * (M.system Pr D x ω).length k) Pr.P) ∧
        (∀ k : ℕ, 2 ≤ k →
          M.nonstatRegretCycle Pr D x k ≤ K * (k : ℝ) ^ (-α) * Real.log k) ∧
        (∀ L : ℕ, 2 ≤ L →
          M.nonstatRegret Pr D x L ≤
            K * ∑ k ∈ Finset.Icc 1 L, (k : ℝ) ^ (-α) * Real.log k) := by sorry

end GOLiQ
