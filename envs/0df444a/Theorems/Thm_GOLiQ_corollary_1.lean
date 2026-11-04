-- Prove2me | Theorems.Thm_GOLiQ_corollary_1
-- name    : GOLiQ.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:05.01641+00:00
-- url     : https://prove2.me/theorems/47222854-db79-4108-b618-5e467eb32d0c
-- title:
--   Corollary 1 — the cycle-$k$ waiting times approach the stationary sequence, (13)
-- statement:
--   Assume the conditions of Theorem 1: Assumptions 1–2, an admissible policy, cycle lengths $D_k\ge1$ and constants $K_2>0$, $0<\alpha\le1$ with (a) $\lceil 6\log k/\min(\gamma,\eta)\rceil\le D_k\le K_2k^{2-\alpha}$ and (b) $\mathbb E\|x_k-x_{k+1}\|^2\le K_2k^{-2\alpha}$. Let $\bar W^k_n$ be the stationary sequence of cycle $k$: $\bar W^k_0$ is drawn independently from the law of $W_\infty(\mu_k,p_k)$ and $\bar W^k_n=(\bar W^k_{n-1}+V^k_n/\mu_k-U^k_n/\lambda_k)^+$ for $1\le n\le D_k$, with $\lambda_k=\lambda(p_k)$. Let $M$ be the constant of Lemma 1.
--
--   There is a constant $A\ge1$, independent of $k$ and $(\mu_k,p_k)$, such that for all $k\ge1$ and $d_k\le n\le D_k$, where $d_k=\lceil 4\log(k+1)/\min(\gamma,\eta)\rceil$,
--   $$\mathbb E\big[|W^k_n-\bar W^k_n|\big]\le e^{-\gamma(n-d_k)}A+2Mk^{-2}.\tag{13}$$
--   As a direct consequence, $I_1=h_0\mathbb E\big[\sum_{n=\tilde d_k+1}^{D_k}(W^k_n-w(\mu_k,p_k))\big]=O(k^{-\alpha})$, with $\tilde d_k=\lceil 5\log k/\min(\gamma,\eta)\rceil$.
--
--   This bounds the transient error in the near-stationary part of each cycle.
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
--   - reading: M, the constant of Lemma 1 → any M for which the bounds of Lemma 1 hold for the queue in question; reason: Lemma 1 supplies such an M; the statement holds for each of them
--   - encoding: W̄₀ᵏ drawn independently from the law of W∞(µₖ, pₖ) → Loynes' supremum at (µₖ, pₖ) over an independent copy (U′, V′) of the primitives; reason: given (µₖ, pₖ) it has the stationary law and is independent of the cycle-k primitives
--   - reading: A independent of k and (µₖ, pₖ) → A chosen after D, K₂, α and before the policy, the copy and M; reason: the literal reading of 'independent of k and (µₖ, pₖ)'
--   - encoding: n ≥ dₖ → dₖ ≤ n ≤ Dₖ; reason: W̄ₙᵏ is defined for n ≤ Dₖ (p.24)
--   - reading: I₁ = O(k^{−α}) → a constant K′ > 0 chosen after the policy with |I₁| ≤ K′k^{−α} for all k ≥ 1; reason: the paper's O-notation
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
--   - encoding: W∞(µ, p), the steady-state waiting time → Loynes' supremum sup_{n≥0} Σ_{j=1}^n (Vⱼ/µ − Uⱼ/λ(p)) on the primitives; reason: it has the stationary law; it is the coupling from the past of p.58
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Corollary 1, p.25; I₁ and d̃ₖ, p.22

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

/-- **Corollary 1** (Chen, Liu, Hong, arXiv:2009.02911v3, p.25): under the conditions of Theorem 1
there is a constant `A ≥ 1` independent of `k` and `(µₖ, pₖ)` such that for all `k ≥ 1` and
`n ≥ dₖ ≡ ⌈4 log(k + 1)/min(γ, η)⌉`,

`E[|Wₙᵏ − W̄ₙᵏ|] ≤ e^{−γ(n−dₖ)} A + 2Mk^{−2}`.    (13)

Here `W̄ₙᵏ` is the stationary sequence of cycle `k` (p.24): `W̄₀ᵏ` is drawn independently from the
steady-state distribution `W∞(µₖ, pₖ)`, and `W̄ₙᵏ = (W̄ₙ₋₁ᵏ + Vₙᵏ/µₖ − Uₙᵏ/λₖ)⁺` for `1 ≤ n ≤ Dₖ`,
with `λₖ = λ(pₖ)`; `M` is the constant of Lemma 1. As a direct consequence, `I₁ = O(k^{−α})`.

**Formalization Note.** The conditions of Theorem 1 are Assumptions 1–2 (with `η` sufficiently
small, as in Lemma 1), an admissible policy, deterministic `Dₖ ≥ 1` and conditions (a), (b) with
constants `K₂ > 0`, `0 < α ≤ 1`. `W̄₀ᵏ` is the Loynes supremum, at the parameter `(µₖ, pₖ)`, over an
independent copy `(U′, V′)` of the primitives. `M` is any constant for which the bounds of Lemma 1
hold for this queue. `A` is chosen after `D`, `K₂`, `α` and before the policy, the copy and `M`.
The range `n ≤ Dₖ` is where `W̄ₙᵏ` is defined. The consequence `I₁ = O(k^{−α})` is the second
conjunct, with `I₁ = h₀E[Σ_{n=d̃ₖ+1}^{Dₖ}(Wₙᵏ − w(µₖ, pₖ))]`, `d̃ₖ = ⌈5 log(k)/min(γ, η)⌉` (p.22), and
`O(k^{−α})` a constant `K′ > 0` chosen after the policy. -/
theorem corollary_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η θ a γ : ℝ, Assumption2 M Pr η θ a γ → η ≤ η₀ →
    ∀ K₂ α : ℝ, 0 < K₂ → 0 < α → α ≤ 1 →
    ∀ D : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → 1 ≤ D k) →
      (∀ k : ℕ, 1 ≤ k →
        ⌈6 * Real.log k / min γ η⌉₊ ≤ D k ∧ (D k : ℝ) ≤ K₂ * (k : ℝ) ^ (2 - α)) →
      ∃ A : ℝ, 1 ≤ A ∧
      ∀ x : ℕ → Ω → Point, M.Admissible Pr D x →
      (∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ‖x k ω - x (k + 1) ω‖ₑ ^ 2 ∂Pr.P ≤ ENNReal.ofReal (K₂ * (k : ℝ) ^ (-2 * α))) →
      (∀ Mc : ℝ, M.MomentBound Pr D x η Mc →
      ∀ U' V' : ℕ → Ω → ℝ, (∀ j, Measurable (U' j)) → (∀ j, Measurable (V' j)) →
        (∀ j, IdentDistrib (U' (j + 1)) (Pr.U 1) Pr.P Pr.P) →
        (∀ j, IdentDistrib (V' (j + 1)) (Pr.V 1) Pr.P Pr.P) →
        iIndepFun (fun i : Fin 5 × ℕ => (![Pr.U, Pr.V, Pr.Z, U', V'] i.1) (i.2 + 1)) Pr.P →
      ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, ⌈4 * Real.log (k + 1) / min γ η⌉₊ ≤ n → n ≤ D k →
        ∫⁻ ω, ENNReal.ofReal |(M.system Pr D x ω).cycleWait k n -
            (lindley
              (loynesWait (fun j => V' j ω / x k ω 0) (fun j => U' j ω / M.lam (x k ω 1))) 0
              (fun j => (M.system Pr D x ω).cycleV k j / x k ω 0)
              (fun j => (M.system Pr D x ω).cycleU k j / M.lam (x k ω 1)) n).1| ∂Pr.P ≤
          ENNReal.ofReal (Real.exp (-γ * ((n : ℝ) - ⌈4 * Real.log (k + 1) / min γ η⌉₊)) * A +
            2 * Mc * (k : ℝ) ^ (-2 : ℤ))) ∧
      ∃ K' : ℝ, 0 < K' ∧ ∀ k : ℕ, 1 ≤ k →
        |M.h0 * ∫ ω, ∑ n ∈ Finset.Icc (⌈5 * Real.log k / min γ η⌉₊ + 1) (D k),
            ((M.system Pr D x ω).cycleWait k n - M.waitMean Pr (x k ω 0) (x k ω 1)) ∂Pr.P| ≤
          K' * (k : ℝ) ^ (-α) := by sorry

end GOLiQ
