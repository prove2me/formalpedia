-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Cocycle_ker_awayMap_le
-- name    : GlobalTheory.SecGlue.Cocycle.ker_awayMap_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:50:12.629282+00:00
-- url     : https://prove2.me/theorems/8ce2c3c6-3188-4054-8bd1-83d95866b2c2
-- title:
--   Cocycle: ker away Map le
-- statement:
--   The Cocycle construction uses the ker away Map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsAgreeOfCocycle.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsAgreeOfCocycle.lean#L30-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsAgreeOfCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Cocycle

theorem GlobalTheory.SecGlue.Cocycle.ker_awayMap_le {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (r : R) :
    RingHom.ker (Localization.awayMap π r) ≤
      (RingHom.ker π).map (algebraMap R (Localization.Away r)) := by sorry
