-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_good_event_dkw
-- name    : InvMarketMaking.LOB.good_event_dkw
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:30.144539+00:00
-- url     : https://prove2.me/theorems/2240b510-8213-482e-95f5-37c4f92b8d1c
-- title:
--   Eq. (13) and p. 34 — with $\psi_t=\min\{1,\sqrt{\log(4T/\delta)/(2t)}\}$ the DKW bands hold for all $t\le T$ w.p. $1-\delta$
-- statement:
--   Let $(V^{\mathrm{sell}}_t,V^{\mathrm{buy}}_t)_{t\ge1}$ be independent valuation pairs, each with law $\mathcal V$, let $F,S$ be the seller c.d.f. and buyer survival function of $\mathcal V$, and $\widehat F_t,\widehat S_t$ the full-feedback estimators of Eq. (12). Let $T\ge1$, $\delta\in(0,1)$ and
--   $$
--   \psi_t(\delta)=\min\Big\{1,\sqrt{\frac{\log(4T/\delta)}{2t}}\Big\}.
--   $$
--   Then, with probability at least $1-\delta$, simultaneously for all $t\in\{1,\dots,T\}$ and all $b,a\in[0,1]$,
--   $$
--   |\widehat F_t(b)-F(b)|\le\psi_t(\delta)\qquad\text{and}\qquad|\widehat S_t(a)-S(a)|\le\psi_t(\delta).
--   $$
--   This is the uniform-in-time confidence band behind the good event (16); with $\delta/3$ in place of $\delta$ it gives the radius $\min\{1,\sqrt{\log(12T/\delta)/(2t)}\}$ of Theorem 6.18.
--
--   Differences from the source:
--   - reading: Eq. (13) states the band for F; footnote 5 and p. 34 assert the analogous band for S and that the good event, which needs both, has probability at least 1 − δ → one event of probability at least 1 − δ carrying both bands; reason: this is the claim of p. 34 for Equation (13), the one the proof of Theorem 6.18 uses
--   - encoding: T rounds of i.i.d. valuation pairs → measurable valuation pairs indexed by ℕ, mutually independent, each with law V; indices 0 and > T unused; reason: the event involves rounds 1, …, T only
--   - encoding: log → Real.log, the natural logarithm; reason: the DKW and Azuma exponents are base e
--   - reading: S(a) = E[I(V^buy ≥ a)] = 1 − F_buy(a) (p. 16) → S(a) = P(V^buy ≥ a); reason: the two expressions differ exactly at atoms of V^buy; the trade probability E[I(V^buy ≥ a)] is what the model and every proof use (p. 59 also writes S(a) = P(−V^buy ≤ −a))
--   - generalization: the valuation law V of Sec. 3 (supported in [0, 1]², P(V^buy = 1) = P(V^sell = 0) = 0) → any probability law V on ℝ²; reason: Theorem 6.1 holds for every law on ℝ, applied to V^sell and to −V^buy; the paper's laws are instances
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Eq. (13), p. 33, and the sentence after Definition 6.4, p. 34

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_IsRoundModel
import Definitions.Def_InvMarketMaking_LOB_goodEvent

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Eq. (13)** with the sentence after Definition 6.4 (Maran, Restelli, Stradi, arXiv:2610.24562v1,
p. 33, Eq. (13), and p. 34). With `ψ_t(δ) = min{1, √(log(4T/δ)/(2t))}`, with probability at least
`1 − δ`, for all `t ∈ [T]`, all `b ∈ [0,1]` and all `a ∈ [0,1]`:
`|F̂_t(b) − F(b)| ≤ ψ_t(δ)` and `|Ŝ_t(a) − S(a)| ≤ ψ_t(δ)`, where `F̂_t, Ŝ_t` are the full-feedback
estimators of Eq. (12).

**Formalization Note** Only the valuation pairs enter: they are measurable, independent across
rounds and each has law `V` (the algorithm's draws `U_t` play no role). `T ≥ 1`, `δ ∈ (0,1)`, and
`log` is the natural logarithm. The bound for `F` is Eq. (13); the bound for `S` is the analogous
one (footnote 5, p. 33), and both hold together, as the good event (16) requires (p. 34). -/
theorem good_event_dkw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (M : Market Ω)
    (hmeas : ∀ t, Measurable (M.Vs t) ∧ Measurable (M.Vb t))
    (hindep : iIndepFun (fun t ω => (M.Vs t ω, M.Vb t ω)) P)
    (hlaw : ∀ t, HasLaw (fun ω => (M.Vs t ω, M.Vb t ω)) V P)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 1) :
    ENNReal.ofReal (1 - δ) ≤ P {ω | ∀ t ∈ Finset.Icc 1 T,
      (∀ b ∈ Set.Icc (0 : ℝ) 1, |empCdf M t b ω - sellCdf V b| ≤
        min 1 (Real.sqrt (Real.log (4 * T / δ) / (2 * t)))) ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1, |empSurv M t a ω - buySurv V a| ≤
        min 1 (Real.sqrt (Real.log (4 * T / δ) / (2 * t))))} := by sorry

end InvMarketMaking.LOB
