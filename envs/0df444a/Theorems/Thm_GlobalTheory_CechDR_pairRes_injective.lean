-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pairRes_injective
-- name    : GlobalTheory.CechDR.pairRes_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:24:50.752902+00:00
-- url     : https://prove2.me/theorems/aeebd1f4-f47d-419e-aba2-68194dfefec8
-- title:
--   Cech DR: pair Res injective
-- statement:
--   The Cech DR construction uses the pair Res injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffinePairRestrictionInjectiveFirstCohomology.lean#L46-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffinePairRestrictionInjectiveFirstCohomology.lean#L46-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR
open Opposite KaehlerDifferential

theorem GlobalTheory.CechDR.pairRes_injective : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧
      Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by sorry
