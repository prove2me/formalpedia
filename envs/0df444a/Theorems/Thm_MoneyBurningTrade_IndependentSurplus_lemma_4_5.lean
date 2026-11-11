-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_lemma_4_5
-- name    : MoneyBurningTrade.IndependentSurplus.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:48.542549+00:00
-- url     : https://prove2.me/theorems/dff97f0b-cd9f-4b90-b89d-a4e68366b74f
-- title:
--   Lemma 4.5 — distributional surplus separation
-- statement:
--   Let $q$ be a separation grid with slack $\tau$, and let $W$ be its normalized mechanism. Let $I\subseteq\{1,\ldots,n-3\}$ be nonempty with $m=|I|$, and let $F$ be any joint probability law on $[0,1]^2$, allowing correlation. Suppose $C>0$, $\varepsilon_1\ge0$ and
--
--   $$\frac C2\le\mathbb E_F[(b-s)^+\mathbf1_{\mathcal R_i}]\le C\ (i\in I),\qquad\mathbb E_F[(b-s)^+\mathbf1_{(\bigcup_{i\in I}\mathcal R_i)^c}]\le\varepsilon_1.$$
--
--   If $h$ is the maximum number of closed intervals $[q_i,q_{i+2}]$, $i\in I$, containing one real price, then
--
--   $$\mathrm{TS}_W(F)>\frac{mC}{4},\qquad \mathrm{TS}_M(F)\le hC+\varepsilon_1$$
--
--   for every measurable randomized DSIC, IR, SBB mechanism $M$ on the full interval. The conclusion also certifies finite objectives for both mechanisms and transfer bounds for the competitor. The bounds are for the actual joint law, not only independent priors.
--
--   Differences from the source:
--   - encoding: expectations of IR and WBB mechanisms on the bounded value square → real integrals accompanied by derived transfer bounds and finite-objective conclusions; reason: equation (9) bounds both payments and surpluses; all admissible competitors remain included
--   - encoding: a distribution F over [0,1]² and first-best contributions written with indicators → a Borel probability measure concentrated on the square and integrals over the exact measurable regions; reason: integration over a set is the indicator integral; correlation, atoms and all source instances are preserved
--   - encoding: nonempty subset of {1,...,n−3} of size m and maximal overlap h → a nonempty finite natural index set with i+3≤n, m=I.card, and the supremum of attainable counts over real prices; reason: the bounded nonempty count set has an attained maximum; closed endpoints are retained
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.5; Appendix A.3, printed p. 25 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_NormalizedMechanism
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_SeparationGrid
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Regions
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Objectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB
import Definitions.Def_SecondBestBT_IsSBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Lemma 4.5 p.25, including both surplus bounds and arbitrary joint priors.
Finiteness is derived for all admissible mechanisms, never required as a hypothesis. -/
theorem lemma_4_5 (G : Grid) (τ : ℝ) (hsep : IsSeparationGrid G τ)
    (I : Finset ℕ) (hI : I.Nonempty)
    (hindices : ∀ i ∈ I, 1 ≤ i ∧ i + 3 ≤ G.n)
    (μ : Measure (ℝ × ℝ)) (hprob : IsProbabilityMeasure μ)
    (hsupport : μ (reportInterval ×ˢ reportInterval)ᶜ = 0)
    (C ε₁ : ℝ) (hC : 0 < C) (hε₁ : 0 ≤ ε₁)
    (hin : ∀ i ∈ I,
      C / 2 ≤ firstBestContribution μ (profileRegion G τ i) ∧
      firstBestContribution μ (profileRegion G τ i) ≤ C)
    (hout : firstBestContribution μ (regionUnion G τ I)ᶜ ≤ ε₁) :
    FiniteObjectives μ (normalizedMechanism G τ) ∧
    (I.card : ℝ) * C / 4 < TS μ (normalizedMechanism G τ) ∧
    ∀ M : SecondBestBT.Mechanism,
      IsMechanism reportInterval M → IsDSIC reportInterval M →
      IsIR reportInterval M → SecondBestBT.IsSBB reportInterval M →
      TransferBounds M ∧ FiniteObjectives μ M ∧
        TS μ M ≤ (overlap G I : ℝ) * C + ε₁ := by sorry

end MoneyBurningTrade.IndependentSurplus
