-- Prove2me | Theorems.Thm_GOLiQ_lemma_6
-- name    : GOLiQ.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:53.415355+00:00
-- url     : https://prove2.me/theorems/ece6dc52-f9a7-487e-8984-514c09653e84
-- title:
--   Lemma 6 — exponential convergence of the observed busy period (corrected: $\mathbb E|X^1_n-X^2_n|^m$ for $0<m\le 2$)
-- statement:
--   Fix $(\mu,p)\in\mathcal B$ and let $X^1_n$, $X^2_n$ be the observed busy periods of two queues coupled as in Lemma 2, whose initial values satisfy $X^1_0,X^2_0\le_{st}\frac{\lambda(\underline p)}{\lambda(\bar p)}\hat X_0$ and $W^1_0,W^2_0\le_{st}\hat W_0$, where $\hat W_0$ and $\hat X_0$ are the stationary waiting time and observed busy period of the dominating queue with $\mu\equiv\underline\mu$, $p\equiv\underline p$. Let $\tau_k=U_k/\lambda(p)$ and $\Gamma_i=\min\{n\ge1:W^i_n=0\}$. Then
--
--   1. $|X^1_n-X^2_n|\le\mathbf 1\{\max(\Gamma_1,\Gamma_2)>n\}\big(\sum_{k=1}^n\tau_k+X^1_0+X^2_0\big)$;
--   2. there is a constant $K_4>0$ such that $\mathbb E\big[|X^1_n-X^2_n|^m\big]\le K_4e^{-0.5\gamma n}n^2$ for all $n\ge1$ and $0<m\le2$.
--
--   This is the analogue of Lemma 2 for the busy periods, which enter the gradient estimator.
--
--   Differences from the source:
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - reading: a sufficiently small constant η > 0 (Assumption 2) → there is η₀ > 0, depending only on the model and the laws of U and V, such that the statement holds for every η ≤ η₀ that satisfies Assumption 2; reason: with η fixed the statement is false: U, V ~ Exp(1), λ(p̲) = 0.99, µ̲ = 1, µ̄ = 2, η = 0.5, θ = 0.005, a = 0.004, γ = 5·10⁻⁶ satisfy Assumption 2, yet under the constant policy (µ̲, p̲) E[exp(ηWₙ)] → E[exp(ηW∞)] = ∞; the proof of Lemma 1 (p.54) needs η below the decay rate η̄ of the dominating queue
--   - encoding: initial values with ≤st bounds → nonnegative random initial values independent of (U, V); ≤st as the order of tail probabilities; Ŵ₀, X̂₀ the Loynes constructions at (µ̲, p̲); reason: ≤st compares laws only
--   - reading: Γᵢ = min{n : Wₙⁱ = 0} → Γᵢ = min{n ≥ 1 : Wₙⁱ = 0}, ∞ if there is none; reason: with n = 0 allowed, W₀¹ = W₀² = 0 and X₀¹ ≠ X₀² violate part 1 at n = 1 while both servers stay busy
--   - generalization: |E[Xₙ¹ − Xₙ²]|^m ≤ K₄e^{−0.5γn}n² for 1 ≤ m ≤ 2 → E[|Xₙ¹ − Xₙ²|^m] ≤ K₄e^{−0.5γn}n²; reason: by Jensen it implies the printed bound for 1 ≤ m ≤ 2; it is the quantity used on p.70
--   - correction: |E[Xₙ¹ − Xₙ²]|^m ≤ K₄e^{−0.5γn}n² for all n ≥ 1 and m ≤ 2 → E[|Xₙ¹ − Xₙ²|^m] ≤ K₄e^{−0.5γn}n² for all n ≥ 1 and real 0 < m ≤ 2; reason: the printed bound is false for small m (and for m ≤ 0): with W₀¹ = W₀² = 0, X₀² = 0 and X₀¹ an independent copy of (λ(p̲)/λ(p̄))X̂₀ (exponential U, V), Γ₁ = Γ₂ = Γ and E[Xₙ¹ − Xₙ²] = E[X₀¹]P(Γ > n) > 0, so |E[·]|^m → 1 as m → 0 while K₄e^{−0.5γn}n² → 0 as n → ∞; the moment form holds for every 0 < m ≤ 2
--   - reading: there exists a constant K₄ > 0 → K₄ uniform in (µ, p) ∈ B and in the initial values; reason: K₄ enters C_D of (36) as a constant (p.70)
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 6, p.65; dominating system, p.53

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Assumption2
import Definitions.Def_GOLiQ_lindley
import Definitions.Def_GOLiQ_Model_objective

open MeasureTheory ProbabilityTheory

namespace GOLiQ

/-- **Lemma 6 (convergence rate of the observed busy period)** (Chen, Liu, Hong,
arXiv:2009.02911v3, e-companion §8.6, p.65): let `Xₙ¹, Xₙ²` be the observed busy periods of two
queues coupled as in Lemma 2, with `X₀¹, X₀² ≤st (λ(p̲)/λ(p̄)) X̂₀` and `W₀¹, W₀² ≤st Ŵ₀`. Then

1. `|Xₙ¹ − Xₙ²| ≤ 1{max(Γ₁, Γ₂) > n} (Σ_{k=1}^n τₖ + X₀¹ + X₀²)`;
2. there is `K₄ > 0` with `E[|Xₙ¹ − Xₙ²|^m] ≤ K₄ e^{−0.5γn} n²` for all `n ≥ 1` and `m ≤ 2`.

Here `τₖ = Uₖ/λ(p)`, `Γᵢ = min{n ≥ 1 : Wₙⁱ = 0}`, and `(Ŵ₀, X̂₀)` are the stationary waiting time and
observed busy period of the dominating queue with `µ ≡ µ̲`, `p ≡ p̲` (proof of Lemma 1, p.53).

**Formalization Note.** The initial values `(W₀ⁱ, X₀ⁱ)` are nonnegative random variables independent
of `(U, V)`; `≤st` is the tail-probability order. `Γᵢ` is the first `n ≥ 1` with `Wₙⁱ = 0` (`∞` if
there is none). Part 2 bounds `E[|Xₙ¹ − Xₙ²|^m]` (the quantity used on p.70; by Jensen it bounds the
printed `|E[Xₙ¹ − Xₙ²]|^m` for `1 ≤ m ≤ 2`) for real `0 < m ≤ 2`, with `K₄` uniform in `(µ, p) ∈ B`
and in the initial values. `η` is read as sufficiently small, as in Lemma 1.

**Correction.** The printed part 2, `|E[Xₙ¹ − Xₙ²]|^m ≤ K₄e^{−0.5γn}n²` for all `m ≤ 2`, is false for
small `m`: with `W₀¹ = W₀² = 0`, `X₀² = 0` and `X₀¹` an independent copy of `(λ(p̲)/λ(p̄))X̂₀`
(exponential `U, V`), `Γ₁ = Γ₂ = Γ` and `E[Xₙ¹ − Xₙ²] = E[X₀¹] P(Γ > n) > 0`, so `|E[·]|^m → 1` as
`m → 0` while `K₄e^{−0.5γn}n² → 0` as `n → ∞`. The moment form `E[|·|^m]` holds for every
`0 < m ≤ 2`. -/
theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η θ a γ : ℝ, Assumption2 M Pr η θ a γ → η ≤ η₀ →
      ∃ K₄ : ℝ, 0 < K₄ ∧
        ∀ mu p : ℝ, mu ∈ Set.Icc M.muLo M.muHi → p ∈ Set.Icc M.pLo M.pHi →
        ∀ Wi₁ Wi₂ Xi₁ Xi₂ : Ω → ℝ,
          Measurable Wi₁ → Measurable Wi₂ → Measurable Xi₁ → Measurable Xi₂ →
          (∀ ω, 0 ≤ Wi₁ ω ∧ 0 ≤ Wi₂ ω ∧ 0 ≤ Xi₁ ω ∧ 0 ≤ Xi₂ ω) →
          IndepFun (fun ω => (Wi₁ ω, Wi₂ ω, Xi₁ ω, Xi₂ ω))
            (fun ω => (fun j => Pr.U j ω, fun j => Pr.V j ω)) Pr.P →
          (∀ t : ℝ, Pr.P {ω | t < Xi₁ ω} ≤
            Pr.P {ω | t < M.lam M.pLo / M.lam M.pHi * M.stationaryBusy Pr M.muLo M.pLo ω}) →
          (∀ t : ℝ, Pr.P {ω | t < Xi₂ ω} ≤
            Pr.P {ω | t < M.lam M.pLo / M.lam M.pHi * M.stationaryBusy Pr M.muLo M.pLo ω}) →
          (∀ t : ℝ, Pr.P {ω | t < Wi₁ ω} ≤ Pr.P {ω | t < M.stationaryWait Pr M.muLo M.pLo ω}) →
          (∀ t : ℝ, Pr.P {ω | t < Wi₂ ω} ≤ Pr.P {ω | t < M.stationaryWait Pr M.muLo M.pLo ω}) →
          let Y₁ : Ω → ℕ → ℝ × ℝ := fun ω =>
            lindley (Wi₁ ω) (Xi₁ ω) (fun j => Pr.V j ω / mu) (fun j => Pr.U j ω / M.lam p)
          let Y₂ : Ω → ℕ → ℝ × ℝ := fun ω =>
            lindley (Wi₂ ω) (Xi₂ ω) (fun j => Pr.V j ω / mu) (fun j => Pr.U j ω / M.lam p)
          let Γ₁ : Ω → ℕ∞ := fun ω => ⨅ m ∈ {m : ℕ | 1 ≤ m ∧ (Y₁ ω m).1 = 0}, (m : ℕ∞)
          let Γ₂ : Ω → ℕ∞ := fun ω => ⨅ m ∈ {m : ℕ | 1 ≤ m ∧ (Y₂ ω m).1 = 0}, (m : ℕ∞)
          (∀ ω (n : ℕ), |(Y₁ ω n).2 - (Y₂ ω n).2| ≤
            (if (n : ℕ∞) < max (Γ₁ ω) (Γ₂ ω) then (1 : ℝ) else 0) *
              (∑ k ∈ Finset.Icc 1 n, Pr.U k ω / M.lam p + Xi₁ ω + Xi₂ ω)) ∧
          (∀ n : ℕ, 1 ≤ n → ∀ m : ℝ, 0 < m → m ≤ 2 →
            ∫⁻ ω, ENNReal.ofReal (|(Y₁ ω n).2 - (Y₂ ω n).2| ^ m) ∂Pr.P ≤
              ENNReal.ofReal (K₄ * Real.exp (-0.5 * γ * n) * (n : ℝ) ^ 2)) := by sorry

end GOLiQ
