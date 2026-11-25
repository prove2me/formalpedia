-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transl_comp_transposeGL
-- name    : GroundTheory.Automorphic.ContragredientTranspose.transl_comp_transposeGL
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:23.758064+00:00
-- url     : https://prove2.me/theorems/50f6512d-eeb7-46bc-8a67-201ec5281c94
-- title:
--   Contragredient Transpose: transl comp transpose GL
-- statement:
--   The Contragredient Transpose construction uses the transl comp transpose GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L386-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L386-L389

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
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
omit [TopologicalSpace F] [IsTopologicalRing F]

theorem GroundTheory.Automorphic.ContragredientTranspose.transl_comp_transposeGL (h : ConjAct (GL (Fin n) F)) (f : GL (Fin n) F → ℂ) :
    (fun x => transl h f (transposeGL x)) = transl (thetaC h) (fun x => f (transposeGL x)) := by sorry
