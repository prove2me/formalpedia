-- Prove2me | Theorems.Thm_GOLiQ_lemma_2
-- name    : GOLiQ.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:05.343383+00:00
-- url     : https://prove2.me/theorems/cf4babb7-d3c1-4cdd-9519-6bbd096959e0
-- title:
--   Lemma 2 — exponential loss of memory of the initial state
-- statement:
--   Let $(\mu,p)\in\mathcal B$ and consider two GI/GI/1 queues with this parameter, synchronously coupled: $W^i_n=(W^i_{n-1}+V_n/\mu-U_n/\lambda(p))^+$ for $i=1,2$ and $n\ge1$, with initial waiting times $W^1_0$, $W^2_0$. For the constants $\gamma,\theta$ of Assumption 2 and any $m\ge1$, conditional on $W^1_0$ and $W^2_0$,
--   $$\mathbb E\big[|W^1_n-W^2_n|^m\,\big|\,W^1_0,W^2_0\big]\le e^{-\gamma n}\big(2+e^{\mu\theta W^1_0}+e^{\mu\theta W^2_0}\big)|W^1_0-W^2_0|^m .$$
--
--   The waiting-time process forgets its initial state at the exponential rate $\gamma$; this bounds the transient error after each policy change.
--
--   Differences from the source:
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - encoding: conditional on W₀¹, W₀² (independent of (U, V)) → deterministic initial values w₁, w₂ ≥ 0; reason: conditioning on initial values independent of the primitives is evaluation at fixed values
--   - reading: any m ≥ 1 → real m ≥ 1; reason: the proof never uses integrality
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 2, p.24

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Assumption2
import Definitions.Def_GOLiQ_lindley

open MeasureTheory

namespace GOLiQ

/-- **Lemma 2 (exponential loss of memory of initial state)** (Chen, Liu, Hong,
arXiv:2009.02911v3, p.24): two GI/GI/1 queues with the same parameter `(µ, p) ∈ B`, synchronously
coupled (`Wₙⁱ = (Wₙ₋₁ⁱ + Vₙ/µ − Uₙ/λ(p))⁺`, `i = 1, 2`) with initial waiting times `W₀¹, W₀²`,
satisfy, for the constants `γ, θ` of Assumption 2 and any `m ≥ 1`,

`E[|Wₙ¹ − Wₙ²|^m | W₀¹, W₀²] ≤ e^{−γn}(2 + e^{µθW₀¹} + e^{µθW₀²}) |W₀¹ − W₀²|^m`.

**Formalization Note.** Conditioning on `W₀¹, W₀²` (independent of `(U, V)`) is encoded by
deterministic initial values `w₁, w₂ ≥ 0`. `m` is real; the bound is stated for every `n ≥ 0`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (η θ a γ : ℝ) (h2 : Assumption2 M Pr η θ a γ)
    (mu p : ℝ) (hmu : mu ∈ Set.Icc M.muLo M.muHi) (hp : p ∈ Set.Icc M.pLo M.pHi)
    (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (m : ℝ) (hm : 1 ≤ m) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal
        (|(lindley w₁ 0 (fun j => Pr.V j ω / mu) (fun j => Pr.U j ω / M.lam p) n).1 -
          (lindley w₂ 0 (fun j => Pr.V j ω / mu) (fun j => Pr.U j ω / M.lam p) n).1| ^ m) ∂Pr.P ≤
      ENNReal.ofReal (Real.exp (-γ * n) *
        (2 + Real.exp (mu * θ * w₁) + Real.exp (mu * θ * w₂)) * |w₁ - w₂| ^ m) := by sorry

end GOLiQ
