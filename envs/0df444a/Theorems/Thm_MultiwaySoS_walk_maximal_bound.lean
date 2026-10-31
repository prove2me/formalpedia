-- Prove2me | Theorems.Thm_MultiwaySoS_walk_maximal_bound
-- name    : MultiwaySoS.walk_maximal_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:22.657842+00:00
-- url     : https://prove2.me/theorems/fb8ed600-7dcf-4d4a-8f27-87f9fe7e2e7e
-- title:
--   Proof of Theorem 2, pp.24–25 (corrected: $\Gamma_{\min}\to\max\{\Gamma^\tau,\Gamma_{\min}\}$) — $\mathbb E[\max_s\Gamma^s]\le\max\{\Gamma^\tau,\Gamma_{\min}\}+3K_1+(K_1/\delta^\prime)H_t$
-- statement:
--   Let $\Gamma^{t+1}=\max\{\Gamma^t+\xi^{t+1}K_1,\Gamma_{\min}\}$ for $t\ge\tau$, where $K_1>0$, $\Gamma_{\min}\in\mathbb R$, the steps $\xi^t\in\{-1,+1\}$ ($t>\tau$) are i.i.d. with $P(\xi^t=+1)=\tfrac12-\delta^\prime$, $\delta^\prime>0$, and are independent of the integrable starting value $\Gamma^\tau$. Let $H_t=\sum_{k=1}^t1/k$ be the $t$-th harmonic number. For every number of steps $t\ge0$,
--   $$\mathbb E\Big[\max_{s\in[\tau,\tau+t]}\Gamma^s\Big]\le\mathbb E[\max\{\Gamma^\tau,\Gamma_{\min}\}]+3K_1+\frac{K_1}{\delta^\prime}H_t .$$
--   With Lemmas 3, 5 and 8 this bounds $\mathbb E[\max_{s\in[t]}(\mathscr Q^s_{im})^-]$, which gives the logarithmic second clause of Theorem 2.
--
--   Differences from the source:
--   - correction: $\mathbb E[\max_{s\in[t]}\Gamma^s]\le\Gamma_{\min}+3K_1+(K_1/\delta^\prime)H_t$ → $\Gamma_{\min}$ replaced by $\mathbb E[\max\{\Gamma^\tau,\Gamma_{\min}\}]$; reason: the printed bound ignores the start: with $\Gamma^\tau=\Gamma_{\min}+100K_1$ and $t=0$ the left side is $\Gamma_{\min}+100K_1$; the paper writes $\max\{\Gamma^\tau,\Gamma_{\min}\}$ for the mean bound on p.24
--   - encoding: $\max_{s\in[t]}$, $t$ steps of the walk → $\max_{s\in[\tau,\tau+t]}$, the start and the next $t$ positions; reason: the walk is indexed from $\tau$; including the start changes nothing since $\Gamma^\tau\le\max\{\Gamma^\tau,\Gamma_{\min}\}$
--   - encoding: $\mathbb E[\max_{s\in[t]}\Psi^s]\le\mathbb E[\max_{s\in[t]}\Gamma^s]\le\dots$ → only the inequality for $\Gamma$; reason: the $\Psi$ part follows from Lemma 3, since the maximum is increasing and convex
--   - generalization: the walk of Lemma 3, started at $\Gamma^\tau=\max\{\Gamma_{\min},K_1\lceil\Upsilon^\tau/K_1\rceil\}$ with $\Gamma_{\min}=K_1(1+\lceil K_2/K_1\rceil)$ → any real boundary $\Gamma_{\min}$ and any integrable start independent of the steps; reason: the bound does not use the lattice $\Gamma_{\min}+K_1\mathbb N$ or the form of $\Gamma_{\min}$; the statement specializes to the paper\'s walk
--   - reading: $\max\{\Gamma^\tau,\Gamma_{\min}\}$ for a possibly random start → $\mathbb E[\max\{\Gamma^\tau,\Gamma_{\min}\}]$; reason: the paper applies the bound with the random start of Lemma 3; for a deterministic start it is the printed term
--   - encoding: steps $\xi^t$ for the finitely many times of the walk → an infinite i.i.d. sequence $\xi^t$, $t>\tau$, on $\Omega^\prime$; reason: the claim depends only on the law of finitely many positions, and a finite sequence extends on a product space with the same law
--   - generalization: $\delta^\prime=\delta/(16\sqrt2n^2K_1(\tau))$ (p.24) → any $\delta^\prime>0$; reason: the bound uses only $\delta^\prime>0$; $\delta^\prime\le1/2$ follows from $P(\xi^t=+1)=\tfrac12-\delta^\prime$
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, proof of Theorem 2, pp.24–25, "E[max_{s∈[t]} Ψ^s] ≤ E[max_{s∈[t]} Γ^s] ≤ Γmin + 3K1 + K1/δ′ Ht"

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MultiwaySoS

/-- Maximal bound for the reflected random walk (arXiv:2112.04622v3, proof of Theorem 2, pp.24–25,
"E[max_{s∈[t]} Γ^s] ≤ Γ_min + 3K₁ + (K₁/δ′) H_t"), corrected: `Γ_min` becomes `max{Γ^τ, Γ_min}`.

For the walk of `walk_mean_bound` and every number of steps `t`, with `H_t` the `t`-th harmonic
number:
`E[max_{s ∈ [τ, τ+t]} Γ^s] ≤ E[max{Γ^τ, Γ_min}] + 3K₁ + (K₁/δ′) H_t`. -/
theorem walk_maximal_bound {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (τ : ℕ) (K₁ g δ' : ℝ) (hK₁ : 0 < K₁) (hδ' : 0 < δ')
    (Γ ξ : ℕ → Ω' → ℝ) (hξmeas : ∀ t, Measurable (ξ t))
    (hΓmeas : Measurable (Γ τ)) (hξval : ∀ t, τ < t → ∀ᵐ ω' ∂P', ξ t ω' = 1 ∨ ξ t ω' = -1)
    (hξlaw : ∀ t, τ < t → (P' {ω' | ξ t ω' = 1}).toReal = 1 / 2 - δ')
    (hindep : iIndepFun (fun k : ℕ => if k = 0 then Γ τ else ξ (τ + k)) P')
    (hint : Integrable (Γ τ) P')
    (hΓ : ∀ t, τ ≤ t → ∀ ω', Γ (t + 1) ω' = max (Γ t ω' + ξ (t + 1) ω' * K₁) g) (t : ℕ) :
    ∫ ω', (Finset.Icc τ (τ + t)).sup' (Finset.nonempty_Icc.mpr (Nat.le_add_right τ t))
        (fun s => Γ s ω') ∂P' ≤
      ∫ ω', max (Γ τ ω') g ∂P' + 3 * K₁ + K₁ / δ' * (harmonic t : ℝ) := by sorry

end MultiwaySoS
