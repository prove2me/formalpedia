-- Prove2me | Theorems.Thm_GlobalTheory_T_affinePairRestriction_injective_firstCohomology
-- name    : GlobalTheory.T.affinePairRestriction_injective_firstCohomology
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:52.278986+00:00
-- url     : https://prove2.me/theorems/5a92fc81-5a57-5f3d-91d7-b7bae47dd5fb
-- title:
--   T: affine Pair Restriction injective first Cohomology
-- statement:
--   The T construction uses the affine Pair Restriction injective first Cohomology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffinePairRestrictionInjectiveFirstCohomologyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffinePairRestrictionInjectiveFirstCohomologyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomology
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomologyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.affinePairRestriction_injective_firstCohomology : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧ Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by sorry
