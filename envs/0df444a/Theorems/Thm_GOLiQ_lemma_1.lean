-- Prove2me | Theorems.Thm_GOLiQ_lemma_1
-- name    : GOLiQ.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:10.685159+00:00
-- url     : https://prove2.me/theorems/89536f77-983e-42ab-b64d-63caa597d67a
-- title:
--   Lemma 1 — uniform boundedness of $W^k_n$, $X^k_n$, $Q_k$ and their exponential moments
-- statement:
--   Suppose Assumptions 1 and 2 hold, with $\eta$ sufficiently small. Then there is a finite constant $M>0$ such that for any policy $(\mu_k,p_k)\in\mathcal B$ and any cycle lengths $D_k\ge1$, for all $k\ge1$, $1\le n\le D_k$ and $1\le m\le4$,
--   $$\mathbb E[(W^k_n)^m],\quad \mathbb E[(X^k_n)^m],\quad \mathbb E[(Q_k)^m],\quad \mathbb E[e^{\eta W^k_n}]\quad\text{and}\quad \mathbb E[e^{\eta Q_k}]$$
--   are all bounded by $M$.
--
--   The bound is uniform in the policy and in the cycle lengths, which is what makes the regret analysis of Theorems 1–3 possible.
--
--   Differences from the source:
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - encoding: x = (µ, p) with the Euclidean norm → a point of EuclideanSpace ℝ (Fin 2), coordinate 0 = µ, 1 = p; reason: the norm of p.12
--   - reading: a sufficiently small constant η > 0 (Assumption 2) → there is η₀ > 0, depending only on the model and the laws of U and V, such that the statement holds for every η ≤ η₀ that satisfies Assumption 2; reason: with η fixed the statement is false: U, V ~ Exp(1), λ(p̲) = 0.99, µ̲ = 1, µ̄ = 2, η = 0.5, θ = 0.005, a = 0.004, γ = 5·10⁻⁶ satisfy Assumption 2, yet under the constant policy (µ̲, p̲) E[exp(ηWₙ)] → E[exp(ηW∞)] = ∞; the proof of Lemma 1 (p.54) needs η below the decay rate η̄ of the dominating queue
--   - reading: the per-cycle indexing of §3.3 with leftovers, recursions (6)–(7) and the price rule of p.15 → one global customer index j = N_{k−1} + n; customer 0 arrives at time 0 to an empty system; customer j pays p_{c(j−1)}, c(i) the last cycle that started strictly before the arrival of customer i; reason: it reproduces (6)–(7) with W₀¹ = 0, Q₁ = 0, and charges the first new arrival of cycle k the old fee p_{k−1}
--   - generalization: any sequences (µₖ, pₖ) ∈ B → any B-valued policy, random or deterministic, possibly anticipating; reason: the domination argument of the proof (p.53) is pathwise; deterministic sequences are a special case
--   - reading: 1 ≤ m ≤ 4 → real m with 1 ≤ m ≤ 4; reason: the proofs never use integrality of m; the real reading is the stronger one
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 1, pp.17–18

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Assumption2
import Definitions.Def_GOLiQ_CycleSystem
import Definitions.Def_GOLiQ_Model_MomentBound

open MeasureTheory

namespace GOLiQ

/-- **Lemma 1 (uniform boundedness of relevant queueing functions)** (Chen, Liu, Hong,
arXiv:2009.02911v3, pp.17–18): under Assumptions 1 and 2 there is a finite `M > 0` such that for any
sequences `(µₖ, pₖ) ∈ B` and `Dₖ ≥ 1`, for all `k ≥ 1`, `1 ≤ n ≤ Dₖ`, `1 ≤ m ≤ 4`, the quantities
`E[(Wₙᵏ)^m]`, `E[(Xₙᵏ)^m]`, `E[(Qₖ)^m]`, `E[exp(ηWₙᵏ)]`, `E[exp(ηQₖ)]` are bounded by `M`.

**Formalization Note.** "A sufficiently small constant `η`" (Assumption 2) is read as: there is
`η₀ > 0` depending only on the model and the laws of `U, V` such that the lemma holds for every
`η ≤ η₀` satisfying Assumption 2 (the proof, p.54, needs `η` below the decay rate `η̄` of the
dominating queue). The policy is any `B`-valued sequence, random or not (the paper's "any
sequences"); `M` is uniform in the policy and in `D`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η θ a γ : ℝ, Assumption2 M Pr η θ a γ → η ≤ η₀ →
      ∃ Mc : ℝ, 0 < Mc ∧ ∀ D : ℕ → ℕ, (∀ k, 1 ≤ k → 1 ≤ D k) →
        ∀ x : ℕ → Ω → Point, (∀ k, 1 ≤ k → ∀ ω, x k ω ∈ M.box) →
          M.MomentBound Pr D x η Mc := by sorry

end GOLiQ
