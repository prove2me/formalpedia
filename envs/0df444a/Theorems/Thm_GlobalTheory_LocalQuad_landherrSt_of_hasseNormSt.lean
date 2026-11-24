-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_landherrSt_of_hasseNormSt
-- name    : GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:12.462908+00:00
-- url     : https://prove2.me/theorems/3d0d4f32-15c4-42d6-be31-b15f233f7862
-- title:
--   Local Quad: landherr St of hasse Norm St
-- statement:
--   The Local Quad construction uses the landherr St of hasse Norm St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LandherrStOfHasseNormSt.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LandherrStOfHasseNormSt.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LandherrStOfHasseNormSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalQuad

theorem GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt : GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.LandherrSt := by sorry
