-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul
-- name    : GroundTheory.Automorphic.ContragredientTranspose.transposeGL_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:17.127895+00:00
-- url     : https://prove2.me/theorems/cd7d5e51-734d-44e5-9aaa-74af0ab5db5e
-- title:
--   Contragredient Transpose: transpose GL smul
-- statement:
--   The Contragredient Transpose construction uses the transpose GL smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L86-L89

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

theorem GroundTheory.Automorphic.ContragredientTranspose.transposeGL_smul (h : ConjAct (GL (Fin n) F)) (x : GL (Fin n) F) :
    transposeGL (h • x) = ConjAct.toConjAct (thetaT (ConjAct.ofConjAct h)) • transposeGL x := by sorry
