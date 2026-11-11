-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_claim_A_1
-- name    : MoneyBurningTrade.IndependentSurplus.claim_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:34.133262+00:00
-- url     : https://prove2.me/theorems/7f4c2e5b-bed3-42d6-82af-7bcc5fba4b02
-- title:
--   Claim A.1 — positive allocations exceed one half
-- statement:
--   Let $q$ be a separation grid with slack $\tau$ as in Definition 4.4, and let $M^{\mathrm{WBB}}$ be its normalized mechanism. At every report profile $(s,b)\in[0,1]^2$ with $\iota_S(s)<\iota_B(b)$,
--
--   $$x(s,b)>\tfrac12.$$
--
--   The separation-grid assumptions include $n\ge4$, $0<\delta\le1/(100n)$, $0<\tau\le\delta L/100$ and (19). The strict bound concerns every positive-allocation profile, with no restriction to a prior's support. It supplies the pointwise probability guarantee used in Claim A.2.
--
--   Differences from the source: none.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Claim A.1, Appendix A.3, printed p. 42 (PDF p. 43); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_NormalizedMechanism
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_SeparationGrid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Claim A.1, Appendix A.3 p.42. The separation-grid assumptions are inherited
from Lemma 4.5; this is not asserted for every grid of Lemma 4.3. -/
theorem claim_A_1 (G : Grid) (τ : ℝ) (hsep : IsSeparationGrid G τ) :
    ∀ s ∈ reportInterval, ∀ b ∈ reportInterval,
      sellerIndex G τ s < buyerIndex G τ b →
      1 / 2 < (normalizedMechanism G τ).x (s, b) := by sorry

end MoneyBurningTrade.IndependentSurplus
