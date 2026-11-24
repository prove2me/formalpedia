-- Prove2me | Theorems.Thm_GlobalTheory_Published_isIntegersLattice_iff
-- name    : GlobalTheory.Published.isIntegersLattice_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:16.250338+00:00
-- url     : https://prove2.me/theorems/18c1f0f7-1295-45a4-86ad-3ea9355e2bb9
-- title:
--   Published: is Integers Lattice iff
-- statement:
--   The Published construction uses the is Integers Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L125-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L125-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
variable [Algebra K ℂ]

theorem GlobalTheory.Published.isIntegersLattice_iff (hp : 0 < p) (h2 : Module.finrank ℚ K = 2) {x : K}
    (hx : x ^ 2 = -(p : K)) (L : PeriodPair) :
    IsIntegersLattice p L ↔ IsIdealLattice (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) L := by sorry
