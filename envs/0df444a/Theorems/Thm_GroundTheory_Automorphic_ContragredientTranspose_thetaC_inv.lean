-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_thetaC_inv
-- name    : GroundTheory.Automorphic.ContragredientTranspose.thetaC_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:17.646447+00:00
-- url     : https://prove2.me/theorems/ef65d51b-b489-4173-affc-6bac6c641f7b
-- title:
--   Contragredient Transpose: theta C inv
-- statement:
--   The Contragredient Transpose construction uses the theta C inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L376-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L376-L377

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

theorem GroundTheory.Automorphic.ContragredientTranspose.thetaC_inv (h : ConjAct (GL (Fin n) F)) : thetaC h⁻¹ = (thetaC h)⁻¹ := by sorry
