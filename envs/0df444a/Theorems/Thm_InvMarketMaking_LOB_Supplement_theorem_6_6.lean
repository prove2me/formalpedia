-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_Supplement_theorem_6_6
-- name    : InvMarketMaking.LOB.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:34:12.475762+00:00
-- url     : https://prove2.me/theorems/a5ce4309-3600-4e3e-8ac4-1179c8de459d
-- title:
--   Theorem 6.6 — on the good event the empirical-Bernstein radius is at most $2\sqrt{2LF(b)(1-F(b))/t}+8L/t$, $L=\log(3|\mathcal B^\circ|T/\delta)$
-- statement:
--   Let $\mathcal V$ be a probability law of the valuation pairs, with seller c.d.f. $F(b)=\mathbb P(V^{\mathrm{sell}}\le b)$. Let $\mathcal B^\circ,\mathcal A^\circ$ be finite subsets of $[0,1]$, let $T\in\mathbb N$ and $\delta$ be given, and write $L=\log(3|\mathcal B^\circ|T/\delta)$. Let $\psi_t(b,\delta)=\sqrt{2\widehat F_t(b)(1-\widehat F_t(b))L/t}+3L/t$ be the empirical-Bernstein radius of Proposition 6.5, with $\widehat F_t$ the empirical c.d.f. of Eq. (12) (and the analogous ask radius). On the good event (16) for these radii, that is, whenever $|F(b)-\widehat F_t(b)|\le\psi_t(b,\delta)$ and $|S(a)-\widehat S_t(a)|\le\psi_t(a,\delta)$ for all $t\in[T]$, $b\in\mathcal B^\circ$, $a\in\mathcal A^\circ$, we have for every $t\in\{1,\dots,T\}$ and every $b\in\mathcal B^\circ$
--   $$
--   \psi_t(b,\delta)\le 2\sqrt{\frac{2L\,F(b)(1-F(b))}{t}}+\frac{8L}{t}.
--   $$
--   So the data-driven radius is, up to constants, no larger than the Bernstein radius built from the unknown variance $F(b)(1-F(b))$. This is the source of the instance-dependent rate in Theorem 6.19.
--
--   Differences from the source:
--   - generalization: the standing model of Sec. 3 (i.i.d. valuation pairs from V with supp V ⊆ [0,1]², P(V^buy = 1) = P(V^sell = 0) = 0) → any valuation sequences and any probability law V; the conclusion holds for every outcome in the good event; reason: Theorem 6.6 is a deterministic inequality on the good event; its proof uses only F(b) ∈ [0,1] and the event's inequalities, so the statement specializes to the source's setting
--   - encoding: 'under the good event' → for every ω ∈ goodEvent V (ebConfig M Bg Ag T δ) M T; reason: the event of Eq. (16) with the radii of Proposition 6.5; the conclusion is pathwise on it
--   - encoding: log → Real.log, the natural logarithm; reason: the concentration exponents are base e
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 6.6, p. 35

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_goodEvent
import Definitions.Def_InvMarketMaking_LOB_Supplement_ebConfig

open MeasureTheory

namespace InvMarketMaking.LOB.Supplement

/-- **Theorem 6.6** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market
Making Under Inventory Constraints, arXiv:2610.24562v1, p. 35). Let `ψ_t(b, δ)` be the radius in
Proposition 6.5. Under the good event, for every `t ∈ [T]` and `b ∈ B°`,
`ψ_t(b, δ) ≤ 2 √(2 log(3|B°|T/δ) F(b)(1 − F(b))/t) + 8 log(3|B°|T/δ)/t`.

**Formalization Note** `B°`, `A°` are finite subsets of `[0, 1]` (Proposition 6.5). The good event is
Eq. (16) with the radii of Proposition 6.5 (`goodEvent V (ebConfig M Bg Ag T δ) M T`), built from the
full-feedback estimators `F̂_t`, `Ŝ_t` of Eq. (12). The conclusion is pathwise, for every outcome in the
good event; no probabilistic assumption on the valuations is needed beyond `V` being a probability
law (so that `F(b) ∈ [0, 1]`). `log` is the natural logarithm. -/
theorem theorem_6_6 {Ω : Type*} (V : Measure (ℝ × ℝ)) [IsProbabilityMeasure V] (M : Market Ω)
    (Bg Ag : Finset ℝ) (hBg : ∀ b ∈ Bg, b ∈ Set.Icc (0 : ℝ) 1) (hAg : ∀ a ∈ Ag, a ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (δ : ℝ) (ω : Ω) (hω : ω ∈ goodEvent V (ebConfig M Bg Ag T δ) M T) :
    ∀ t ∈ Finset.Icc 1 T, ∀ b ∈ Bg,
      (ebConfig M Bg Ag T δ).ψF t b ω ≤
        2 * Real.sqrt (2 * Real.log (3 * Bg.card * T / δ) * sellCdf V b * (1 - sellCdf V b) / t) +
          8 * Real.log (3 * Bg.card * T / δ) / t := by sorry

end InvMarketMaking.LOB.Supplement
