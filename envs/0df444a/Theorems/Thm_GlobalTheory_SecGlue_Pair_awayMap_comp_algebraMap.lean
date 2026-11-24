-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Pair_awayMap_comp_algebraMap
-- name    : GlobalTheory.SecGlue.Pair.awayMap_comp_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:52:58.51309+00:00
-- url     : https://prove2.me/theorems/b032f5ad-b7bc-433b-a78f-292486d1d548
-- title:
--   Pair: away Map comp algebra Map
-- statement:
--   The Pair construction uses the away Map comp algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L82-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Pair

theorem GlobalTheory.SecGlue.Pair.awayMap_comp_algebraMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    (Localization.awayMap π c).comp (algebraMap R (Localization.Away c)) =
      (algebraMap R₀ (Localization.Away (π c))).comp π := by sorry
