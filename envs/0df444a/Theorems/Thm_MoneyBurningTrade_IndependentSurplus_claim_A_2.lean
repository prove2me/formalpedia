-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_claim_A_2
-- name    : MoneyBurningTrade.IndependentSurplus.claim_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:46.842296+00:00
-- url     : https://prove2.me/theorems/d37b4bed-7c5f-43f9-b863-4233174e24ab
-- title:
--   Claim A.2 — WBB surplus and SBB price bound
-- statement:
--   Let $q$ be a separation grid with slack $\tau$, and let $W$ be its normalized WBB mechanism. For every measurable randomized DSIC, IR, SBB competitor $M$ on $[0,1]$, there is a probability law $\mu$ over real posted prices such that $x_M(s,b)\le\mu([s,b])$ at every profile. For each $1\le i\le n-3$ and each $(s,b)\in\mathcal R_i$,
--
--   $$\mathrm{TS}_W(s,b)>\frac{b-s}{2},\qquad \mathrm{TS}_M(s,b)\le(b-s)\mu([q_i,q_{i+2}]).$$
--
--   The region is the exact half-open rectangle of Definition 4.4. The existence of the price law is included in the conclusion, as stated using [ČP16] in the source; it is not an additional assumption on the SBB competitor. This connects pointwise mechanism validity to the distributional comparison.
--
--   Differences from the source:
--   - encoding: the assertion “By [ČP16]” that a posted-price law dominates the SBB allocation → an explicit existential probability measure satisfying that pointwise domination together with both region inequalities; reason: the source includes this assertion; writing it as a conclusion does not narrow the universally quantified SBB mechanism class
--   - encoding: 1 ≤ i ≤ n−3 → 1 ≤ i and i+3 ≤ n; reason: equivalent bounds on natural indices avoid a truncated subtraction at the boundary
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Claim A.2, Appendix A.3, printed p. 42–43 (PDF p. 43–44); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_NormalizedMechanism
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_SeparationGrid
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Regions
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Objectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_SecondBestBT_IsSBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Claim A.2, Appendix A.3 pp.42–43. The posted-price domination is a
conclusion for every SBB competitor, rather than an extra hypothesis. -/
theorem claim_A_2 (G : Grid) (τ : ℝ) (hsep : IsSeparationGrid G τ)
    (M : SecondBestBT.Mechanism) (hM : IsMechanism reportInterval M)
    (hdsic : IsDSIC reportInterval M) (hir : IsIR reportInterval M)
    (hsbb : SecondBestBT.IsSBB reportInterval M) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ s ∈ reportInterval, ∀ b ∈ reportInterval,
        M.x (s, b) ≤ μ.real (Set.Icc s b)) ∧
      ∀ i : ℕ, 1 ≤ i → i + 3 ≤ G.n →
        ∀ p ∈ profileRegion G τ i,
          (p.2 - p.1) / 2 < tradersSurplus (normalizedMechanism G τ) p ∧
          tradersSurplus M p ≤ (p.2 - p.1) * μ.real (Set.Icc (G.q i) (G.q (i + 2))) := by sorry

end MoneyBurningTrade.IndependentSurplus
