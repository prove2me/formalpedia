-- Prove2me | Theorems.Thm_MarketMakerAds_proof_theorem_1_step_1
-- name    : MarketMakerAds.proof_theorem_1_step_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:59.208559+00:00
-- url     : https://prove2.me/theorems/356f286f-1442-49a5-bcb6-1edab041c9bf
-- title:
--   Proof of Theorem 1, Step 1 — $\mu_{\mathrm{lie}}=\mu_{\mathrm{truth}}-\delta$ and $\mathrm{Var}_{\mathrm{lie}}=\mathrm{Var}_{\mathrm{truth}}-\Delta$
-- statement:
--   A buyer with value $v$ faces an auction clearing price $p$ with law $h$, which its own report does not move. Reporting $b$ (the paper's $v'$), it wins exactly when $p\in W$, where $W=\{p<b\}$ or $W=\{p\le b\}$, and then pays $p$. Let
--
--   $$
--   X_{\mathrm{truth}}(p)=(v-p)^+,\qquad X_{\mathrm{lie}}(p)=\begin{cases}v-p,&p\in W,\\0,&p\notin W,\end{cases}
--   $$
--
--   with means $\mu_{\mathrm{truth}},\mu_{\mathrm{lie}}$ and variances $\mathrm{Var}_{\mathrm{truth}},\mathrm{Var}_{\mathrm{lie}}$ under $h$. Put
--
--   $$
--   \delta=\mathbf E\big[X_{\mathrm{truth}}-X_{\mathrm{lie}}\big],\qquad \Delta=\mathbf E\big[X_{\mathrm{truth}}^2-X_{\mathrm{lie}}^2\big]-2\,\delta\,\mu_{\mathrm{truth}}+\delta^2 .
--   $$
--
--   If the negative part of $p$ has a finite second moment, then
--
--   $$
--   \mu_{\mathrm{lie}}=\mu_{\mathrm{truth}}-\delta\qquad\text{and}\qquad \mathrm{Var}_{\mathrm{lie}}=\mathrm{Var}_{\mathrm{truth}}-\Delta .
--   $$
--
--   For $b<v$ and for $b>v$, $\delta$ and $\Delta$ are the paper's $\int_{v'}^{v}(v-p)h(p)\,dp$ and $\int_{v'}^{v}(v-p)^2h(p)\,dp-2\delta\mu_{\mathrm{truth}}+\delta^2$. These identities are Step 1 of the proof that the $(I+1)$-th price auction is truthful in expectation under mean-variance utility.
--
--   Differences from the source:
--   - generalization: a clearing-price density $h$ on $[0,\infty)$ → any probability law on $\mathbb R$ whose negative part has a finite second moment; reason: the identities only use finiteness of the integrals; every law on $[0,\infty)$ satisfies the hypothesis.
--   - generalization: two cases, $v'<v$ (p.31) and $v'>v$ (p.33), with oriented integrals $\int_{v'}^{v}$ → one statement for every report $b$, with $\delta,\Delta$ written through $X_{\mathrm{truth}}-X_{\mathrm{lie}}$ and $X_{\mathrm{truth}}^2-X_{\mathrm{lie}}^2$; reason: in both cases these equal the printed integrals, and $b=v$ is included.
--   - generalization: ties at $p=b$ not specified (a density gives them probability 0) → either tie rule, win set $\{p<b\}$ or $\{p\le b\}$; reason: covers both deterministic tie rules; under a density they coincide.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Appendix B, Proof of Theorem 1, Step 1, p.31 (underbidding) and p.33 (overbidding)

import Mathlib

open MeasureTheory

namespace MarketMakerAds

/-- **Proof of Theorem 1, Step 1 (pp.31, 33): `µ_lie = µ_truth − δ` and `Var_lie = Var_truth − ∆`.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Appendix B,
Proof of Theorem 1, Step 1, p.31 (underbidding) and p.33 (overbidding): "µ_lie = µ_truth − δ and
Var_lie = Var_truth − ∆, where δ = ∫_{v'}^{v} (v − p) · h(p) · dp and
∆ = ∫_{v'}^{v} (v − p)² · h(p) · dp − 2 · δ · µ_truth + δ²."

A buyer with value `v` faces a clearing price `p ~ h` and reports `b` (the paper's `v'`). It wins
iff `p ∈ W`, where `W` is `{p < b}` or `{p ≤ b}` (either tie rule), and then pays `p`. Its payoff
is `X_lie(p) = v − p` on `W` and `0` otherwise; the truthful payoff is `X_truth(p) = (v − p)⁺`.

**Formalization Note** `δ` and `∆` are written as `∫ (X_truth − X_lie) dh` and
`∫ (X_truth² − X_lie²) dh − 2δµ_truth + δ²`; for `b < v` and `b > v` these are the printed
oriented integrals `∫_{v'}^{v}` (up to the tie at `p = b`, which the printed integrals over a
density ignore). The law `h` is any probability measure on `ℝ` whose negative part has a finite
second moment (the paper's `h` lives on `[0, ∞)`). The printed last display of Step 1 has a
duplicated factor `h(p)`, which is a typo. -/
theorem proof_theorem_1_step_1 (h : Measure ℝ) [IsProbabilityMeasure h]
    (hneg : Integrable (fun p => (max (-p) 0) ^ 2) h)
    (v b : ℝ) (W : Set ℝ) (hW₁ : Set.Iio b ⊆ W) (hW₂ : W ⊆ Set.Iic b) :
    let Xt : ℝ → ℝ := fun p => max (v - p) 0
    let Xl : ℝ → ℝ := W.indicator fun p => v - p
    let μt := ∫ p, Xt p ∂h
    let μl := ∫ p, Xl p ∂h
    let Vt := ∫ p, (Xt p - μt) ^ 2 ∂h
    let Vl := ∫ p, (Xl p - μl) ^ 2 ∂h
    let δ := ∫ p, (Xt p - Xl p) ∂h
    let Δ := (∫ p, (Xt p ^ 2 - Xl p ^ 2) ∂h) - 2 * δ * μt + δ ^ 2
    μl = μt - δ ∧ Vl = Vt - Δ := by sorry

end MarketMakerAds
