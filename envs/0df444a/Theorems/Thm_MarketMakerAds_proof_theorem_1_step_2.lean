-- Prove2me | Theorems.Thm_MarketMakerAds_proof_theorem_1_step_2
-- name    : MarketMakerAds.proof_theorem_1_step_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:02.139067+00:00
-- url     : https://prove2.me/theorems/dbb9dbe1-b21e-404f-a24a-8017697d5958
-- title:
--   Proof of Theorem 1, Step 2, (6)/(9) — $\Delta/\mathrm{Var}_{\mathrm{truth}}\le\delta/\mu_{\mathrm{truth}}$
-- statement:
--   In the setting of Step 1 (value $v$, report $b$, win set $W=\{p<b\}$ or $\{p\le b\}$, clearing price $p\sim h$ whose negative part has a finite second moment, truthful payoff $(v-p)^+$, misreport payoff $v-p$ on $W$ and $0$ off $W$), let $\mu_{\mathrm{truth}}$ and $\mathrm{Var}_{\mathrm{truth}}$ be the mean and variance of the truthful payoff and $\delta,\Delta$ as in Step 1. Then
--
--   1. $\delta\ge0$;
--   2. if $b\le v$ (underbidding), $\delta\le\mu_{\mathrm{truth}}$;
--   3. for every $b$,
--
--   $$
--   \Delta\cdot\mu_{\mathrm{truth}}\le\delta\cdot\mathrm{Var}_{\mathrm{truth}},
--   $$
--
--   which is the paper's inequality $\dfrac{\Delta}{\mathrm{Var}_{\mathrm{truth}}}\le\dfrac{\delta}{\mu_{\mathrm{truth}}}$ when both denominators are positive.
--
--   When $\Delta\ge0$, the relative variance reduction from misreporting is at most the relative mean reduction. This is the key inequality behind truthfulness in expectation under mean-variance utility.
--
--   Differences from the source:
--   - encoding: $\Delta/\mathrm{Var}_{\mathrm{truth}}\le\delta/\mu_{\mathrm{truth}}$ → $\Delta\,\mu_{\mathrm{truth}}\le\delta\,\mathrm{Var}_{\mathrm{truth}}$; reason: equivalent where the printed quotients are defined ($\mu_{\mathrm{truth}},\mathrm{Var}_{\mathrm{truth}}>0$), and stated without dividing by zero otherwise.
--   - generalization: a clearing-price density $h$ on $[0,\infty)$ → any probability law on $\mathbb R$ whose negative part has a finite second moment; reason: every law on $[0,\infty)$ satisfies the hypothesis.
--   - generalization: the two cases $v'<v$ ((6), p.32) and $v'>v$ ((9), p.33) → one statement for every report $b$ and either tie rule at $p=b$; reason: specializes to both printed cases.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Appendix B, Proof of Theorem 1, Step 2, eq. (6), p.32 and eq. (9), p.33; δ ≥ 0 pp.31, 33; δ ≤ µ_truth p.32

import Mathlib

open MeasureTheory

namespace MarketMakerAds

/-- **Proof of Theorem 1, Step 2, (6) p.32 and (9) p.33: `∆ / Var_truth ≤ δ / µ_truth`.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Appendix B,
Proof of Theorem 1, Step 2, eq. (6), p.32 (underbidding) and eq. (9), p.33 (overbidding):
"We next show the following inequality that relates δ and ∆: ∆ / Var_truth ≤ δ / µ_truth."
Also used there: "δ ≥ 0" (pp.31, 33) and "δ ≤ µ_truth" (p.32, underbidding).

Setting as in Step 1: value `v`, report `b`, win set `W` (`{p < b}` or `{p ≤ b}`), clearing
price `p ~ h`, truthful payoff `(v − p)⁺`, misreport payoff `v − p` on `W` and `0` off `W`.

**Formalization Note** (6) is stated multiplied out, `∆ · µ_truth ≤ δ · Var_truth`, which needs no
positivity of `µ_truth` or `Var_truth` and is equivalent to (6) when both are positive. It is stated
for every report `b`, below or above `v`. `δ ≤ µ_truth` is stated for underbidding `b ≤ v`, where
the paper uses it; for overbidding it can fail. `h` is any probability law on `ℝ` whose negative
part has a finite second moment. -/
theorem proof_theorem_1_step_2 (h : Measure ℝ) [IsProbabilityMeasure h]
    (hneg : Integrable (fun p => (max (-p) 0) ^ 2) h)
    (v b : ℝ) (W : Set ℝ) (hW₁ : Set.Iio b ⊆ W) (hW₂ : W ⊆ Set.Iic b) :
    let Xt : ℝ → ℝ := fun p => max (v - p) 0
    let Xl : ℝ → ℝ := W.indicator fun p => v - p
    let μt := ∫ p, Xt p ∂h
    let Vt := ∫ p, (Xt p - μt) ^ 2 ∂h
    let δ := ∫ p, (Xt p - Xl p) ∂h
    let Δ := (∫ p, (Xt p ^ 2 - Xl p ^ 2) ∂h) - 2 * δ * μt + δ ^ 2
    0 ≤ δ ∧ (b ≤ v → δ ≤ μt) ∧ Δ * μt ≤ δ * Vt := by sorry

end MarketMakerAds
