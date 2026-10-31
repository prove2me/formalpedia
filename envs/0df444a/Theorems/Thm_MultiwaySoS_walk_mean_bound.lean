-- Prove2me | Theorems.Thm_MultiwaySoS_walk_mean_bound
-- name    : MultiwaySoS.walk_mean_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:20.852987+00:00
-- url     : https://prove2.me/theorems/3649bbb5-c515-4b1a-ac7f-7729c7de43d6
-- title:
--   Proof of Theorem 2, p.24 — $\mathbb E[\Gamma^t]\le\max\{\Gamma^\tau,\Gamma_{\min}\}+K_1\rho/(1-\rho)$ for the reflected walk
-- statement:
--   Let $\Gamma^{t+1}=\max\{\Gamma^t+\xi^{t+1}K_1,\Gamma_{\min}\}$ for $t\ge\tau$, where $K_1>0$, $\Gamma_{\min}\in\mathbb R$, the steps $\xi^t\in\{-1,+1\}$ ($t>\tau$) are i.i.d. with $P(\xi^t=+1)=\tfrac12-\delta^\prime$, $\delta^\prime>0$, and are independent of the integrable starting value $\Gamma^\tau$. With $\rho=(1-2\delta^\prime)/(1+2\delta^\prime)$, for every $t\ge\tau$,
--   $$\mathbb E[\Gamma^t]\le\mathbb E[\max\{\Gamma^\tau,\Gamma_{\min}\}]+K_1\frac{\rho}{1-\rho}.$$
--   With Lemmas 3 and 8 this bounds $\mathbb E[\Psi^t]$, hence the expected virtual queues, which gives the first clause of Theorem 2.
--
--   Differences from the source:
--   - generalization: the walk of Lemma 3, started at $\Gamma^\tau=\max\{\Gamma_{\min},K_1\lceil\Upsilon^\tau/K_1\rceil\}$ with $\Gamma_{\min}=K_1(1+\lceil K_2/K_1\rceil)$ → any real boundary $\Gamma_{\min}$ and any integrable start independent of the steps; reason: the bound does not use the lattice $\Gamma_{\min}+K_1\mathbb N$ or the form of $\Gamma_{\min}$; the statement specializes to the paper\'s walk
--   - reading: $\max\{\Gamma^\tau,\Gamma_{\min}\}$ for a possibly random start → $\mathbb E[\max\{\Gamma^\tau,\Gamma_{\min}\}]$; reason: the paper applies the bound with the random start of Lemma 3; for a deterministic start it is the printed term
--   - encoding: "$=O(n^2\tau^4/\delta)$" after the bound → not stated; reason: it concerns the constants of Lemma 8, not the walk
--   - encoding: steps $\xi^t$ for the finitely many times of the walk → an infinite i.i.d. sequence $\xi^t$, $t>\tau$, on $\Omega^\prime$; reason: the claim depends only on the law of finitely many positions, and a finite sequence extends on a product space with the same law
--   - generalization: $\delta^\prime=\delta/(16\sqrt2n^2K_1(\tau))$ (p.24) → any $\delta^\prime>0$; reason: the bound uses only $\delta^\prime>0$; $\delta^\prime\le1/2$ follows from $P(\xi^t=+1)=\tfrac12-\delta^\prime$
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, proof of Theorem 2, p.24, "a simple coupling argument shows that we can bound E[Γ^t] ≤ max{Γ^τ, Γmin} + K1 ρ/(1 − ρ)"

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MultiwaySoS

/-- Mean bound for the reflected random walk (arXiv:2112.04622v3, proof of Theorem 2, p.24: "Since
the random walk {Γ^t} starts at Γ^τ, and not in steady state, a simple coupling argument shows that
we can bound E[Γ^t] ≤ max{Γ^τ, Γ_min} + K₁ ρ/(1 − ρ)").

Let `Γ^{t+1} = max{Γ^t + ξ^{t+1}K₁, Γ_min}` for `t ≥ τ`, where `K₁ > 0`, the steps `ξ^t ∈ {−1, +1}`
(`t > τ`) are i.i.d. with `P(ξ^t = +1) = 1/2 − δ′`, `δ′ > 0`, independent of the integrable
start `Γ^τ`. With `ρ = (1 − 2δ′)/(1 + 2δ′)`, for every `t ≥ τ`:
`E[Γ^t] ≤ E[max{Γ^τ, Γ_min}] + K₁ ρ/(1 − ρ)`.

**Formalization Note.** `Γ_min` is any real number `g` and the start is any integrable random
variable (for a deterministic start the right side is the printed one). The `= O(n²τ⁴/δ)` that
follows on p.24 concerns the constants of Lemma 8 and is not part of this statement. -/
theorem walk_mean_bound {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (τ : ℕ) (K₁ g δ' : ℝ) (hK₁ : 0 < K₁) (hδ' : 0 < δ')
    (Γ ξ : ℕ → Ω' → ℝ) (hξmeas : ∀ t, Measurable (ξ t))
    (hΓmeas : Measurable (Γ τ)) (hξval : ∀ t, τ < t → ∀ᵐ ω' ∂P', ξ t ω' = 1 ∨ ξ t ω' = -1)
    (hξlaw : ∀ t, τ < t → (P' {ω' | ξ t ω' = 1}).toReal = 1 / 2 - δ')
    (hindep : iIndepFun (fun k : ℕ => if k = 0 then Γ τ else ξ (τ + k)) P')
    (hint : Integrable (Γ τ) P')
    (hΓ : ∀ t, τ ≤ t → ∀ ω', Γ (t + 1) ω' = max (Γ t ω' + ξ (t + 1) ω' * K₁) g) (t : ℕ) (ht : τ ≤ t) :
    ∫ ω', Γ t ω' ∂P' ≤
      ∫ ω', max (Γ τ ω') g ∂P' + K₁ * ((1 - 2 * δ') / (1 + 2 * δ')) /
        (1 - (1 - 2 * δ') / (1 + 2 * δ')) := by sorry

end MultiwaySoS
