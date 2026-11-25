-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_thetaT_apply
-- name    : GroundTheory.Automorphic.ContragredientTranspose.thetaT_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:36:18.266416+00:00
-- url     : https://prove2.me/theorems/13265aa1-9c8d-4942-8c1a-4b21ee31b472
-- title:
--   Contragredient Transpose: theta T apply
-- statement:
--   The Contragredient Transpose construction uses the theta T apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L84-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L84-L84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.thetaT_apply (g : GL (Fin n) F) : thetaT g = (transposeGL g)⁻¹ := by sorry
