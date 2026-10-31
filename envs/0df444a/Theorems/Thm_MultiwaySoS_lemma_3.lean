-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_3
-- name    : MultiwaySoS.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:33.790685+00:00
-- url     : https://prove2.me/theorems/9f65dcc4-55b1-4d7a-90f4-b0639d70ab8a
-- title:
--   Lemma 3 — a process with bounded increments and negative drift is dominated by a reflected random walk in increasing convex order
-- statement:
--   Let $\{\Upsilon^t\}$ be adapted to a filtration $\{\mathcal F^t\}$ on $(\Omega,P)$, with $\Upsilon^\tau$ integrable, and for $\tau\le t<T$:
--
--   1. (bounded variation) $|\Upsilon^{t+1}-\Upsilon^t|\le K_1$ almost surely;
--   2. (expected decrease) $\mathbb E[\Upsilon^{t+1}-\Upsilon^t\mid\mathcal F^t]\le-2\delta^\prime K_1$ on $\{\Upsilon^t\ge K_2\}$.
--
--   Let $\{\Gamma^t\}$ on $(\Omega^\prime,P^\prime)$ be the reflected random walk with step size $K_1>0$, reflection boundary $\Gamma_{\min}=K_1(1+\lceil K_2/K_1\rceil)$, initial value $\Gamma^\tau$ distributed as $\max\{\Gamma_{\min},K_1\lceil\Upsilon^\tau/K_1\rceil\}$, and
--   $$\Gamma^{t+1}=\max\{\Gamma^t+\xi^{t+1}K_1,\Gamma_{\min}\},\qquad t=\tau,\dots,T-1,$$
--   where the $\xi^t\in\{-1,+1\}$ ($t>\tau$) are i.i.d., independent of $\Gamma^\tau$, with $P^\prime(\xi^t=+1)=\tfrac12-\delta^\prime$. Then
--   $$\{\Upsilon^t\}_{t\in[\tau,T]}\le_{icx}\{\Gamma^t\}_{t\in[\tau,T]},$$
--   that is, $\mathbb E[f(\Upsilon^\tau,\dots,\Upsilon^T)]\le\mathbb E[f(\Gamma^\tau,\dots,\Gamma^T)]$ for every increasing convex $f$ for which both expectations exist.
--
--   This comparison gives the $1/\delta$ rate of Theorem 2, where Hajek's bound would give $1/\delta^2$.
--
--   Differences from the source:
--   - encoding: a conditional expectation given $\mathcal F^t$ on the event $\{\cdot\ge K_2\}$ → its defining form: $\int_A(\cdot)\,dP\le c\,P(A)$ for every $A\in\mathcal F^t$ contained in the event; reason: equivalent for integrable increments; avoids the junk value of an undefined conditional expectation
--   - reading: "Let $\{\Gamma^t\}$ be a reflected random walk … initial condition $\Gamma^\tau=\max\{\Gamma_{\min},K_1\lceil\Upsilon^\tau/K_1\rceil\}$" → $\Gamma$ on its own probability space, with $\Gamma^\tau$ equal in law to $\max\{\Gamma_{\min},K_1\lceil\Upsilon^\tau/K_1\rceil\}$ and the steps independent of $\Gamma^\tau$; reason: $\le_{icx}$ compares laws (Definition 1), so the walk need not live on $\Omega$; independence of the steps from the start is part of "random walk"
--   - reading: Definition 1, "random vectors with finite expectations" → $\Upsilon^\tau$ integrable; the order is the published `IcxOrder` (expectations of increasing convex $f$ where both exist); reason: finite expectations of the other coordinates follow from (a); `IcxOrder` is the first sentence of Definition 1 with no added condition
--   - encoding: the vectors $\{\Upsilon^t\}_{t\in[\tau,T]}$, $\{\Gamma^t\}_{t\in[\tau,T]}$ → vectors indexed by `Fin (T - τ + 1)`, entry $k$ being time $\tau+k$; reason: the same vectors; for $T<\tau$ the truncated length gives the single time $\tau$
--   - reading: (a), (b) with no range of $t$ → for $\tau\le t<T$; reason: the comparison is on $[\tau,T]$; other times play no part
--   - encoding: "step size $K_1$" → $K_1>0$; reason: the page divides by $K_1$ and uses it as a step of the walk
--   - encoding: steps $\xi^t$ for the finitely many times of the walk → an infinite i.i.d. sequence $\xi^t$, $t>\tau$, on $\Omega^\prime$; reason: the claim depends only on the law of finitely many positions, and a finite sequence extends on a product space with the same law
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 3, p.12; Definition 1, p.12

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_IcxOrder

open MeasureTheory ProbabilityTheory

namespace MultiwaySoS

/-- Lemma 3 (arXiv:2112.04622v3, p.12): domination of a drifting process by a reflected random walk
in increasing convex order.

Let `{Υ^t}` be adapted to a filtration `{F^t}` on `(Ω, P)`, with `Υ^τ` integrable, and for
`τ ≤ t < T`:
(a) `|Υ^{t+1} − Υ^t| ≤ K₁` almost surely;
(b) `E[Υ^{t+1} − Υ^t | F^t] ≤ −2δ′K₁` on `{Υ^t ≥ K₂}`.
Let `{Γ^t}` on `(Ω', P')` be the reflected random walk with step `K₁ > 0`, boundary
`Γ_min = K₁(1 + ⌈K₂/K₁⌉)`, initial value `Γ^τ` distributed as `max{Γ_min, K₁⌈Υ^τ/K₁⌉}`, and
`Γ^{t+1} = max{Γ^t + ξ^{t+1}K₁, Γ_min}` (`t = τ, …, T − 1`), where the `ξ^t ∈ {−1, +1}` are i.i.d.,
independent of `Γ^τ`, with `P'(ξ^t = +1) = 1/2 − δ′`. Then
`{Υ^t}_{t ∈ [τ, T]} ≤_icx {Γ^t}_{t ∈ [τ, T]}`.

**Formalization Note.** (b) is in the defining form of the conditional expectation (set integrals
over `A ∈ F^t`, `A ⊆ {Υ^t ≥ K₂}`). The two vectors `(Υ^τ, …, Υ^T)`, `(Γ^τ, …, Γ^T)` are indexed by
`Fin (T − τ + 1)`; the order is the published `IcxOrder` (Definition 1, first sentence). "i.i.d.
and independent of `Γ^τ`" is mutual independence of the family `Γ^τ, ξ^{τ+1}, ξ^{τ+2}, …`. No sign
is imposed on `δ′`, as on the page; `P'(ξ^t = +1) = 1/2 − δ′` forces `|δ′| ≤ 1/2`. -/
theorem lemma_3 {Ω Ω' : Type*} {m0 : MeasurableSpace Ω} [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P'] (F : Filtration ℕ m0)
    (Υ : ℕ → Ω → ℝ) (hadapt : ∀ t, Measurable[F t] (Υ t)) (τ T : ℕ) (K₁ K₂ δ' : ℝ)
    (hK₁ : 0 < K₁) (hint : Integrable (Υ τ) P)
    (ha : ∀ t, τ ≤ t → t < T → ∀ᵐ ω ∂P, |Υ (t + 1) ω - Υ t ω| ≤ K₁)
    (hb : ∀ t, τ ≤ t → t < T → ∀ A : Set Ω, MeasurableSet[F t] A → A ⊆ {ω | K₂ ≤ Υ t ω} →
      ∫ ω in A, (Υ (t + 1) ω - Υ t ω) ∂P ≤ -(2 * δ' * K₁) * (P A).toReal)
    (Γ ξ : ℕ → Ω' → ℝ) (hξmeas : ∀ t, Measurable (ξ t)) (hΓmeas : Measurable (Γ τ))
    (hξval : ∀ t, τ < t → ∀ᵐ ω' ∂P', ξ t ω' = 1 ∨ ξ t ω' = -1)
    (hξlaw : ∀ t, τ < t → (P' {ω' | ξ t ω' = 1}).toReal = 1 / 2 - δ')
    (hindep : iIndepFun (fun k : ℕ => if k = 0 then Γ τ else ξ (τ + k)) P')
    (hΓ0 : P'.map (Γ τ) =
      P.map (fun ω => max (K₁ * (1 + (⌈K₂ / K₁⌉ : ℝ))) (K₁ * (⌈Υ τ ω / K₁⌉ : ℝ))))
    (hΓ : ∀ t, τ ≤ t → t < T → ∀ ω',
      Γ (t + 1) ω' = max (Γ t ω' + ξ (t + 1) ω' * K₁) (K₁ * (1 + (⌈K₂ / K₁⌉ : ℝ)))) :
    StochasticOrders.MultivariateVariability.IcxOrder P P'
      (fun ω (k : Fin (T - τ + 1)) => Υ (τ + k) ω) (fun ω' k => Γ (τ + k) ω') := by sorry

end MultiwaySoS
