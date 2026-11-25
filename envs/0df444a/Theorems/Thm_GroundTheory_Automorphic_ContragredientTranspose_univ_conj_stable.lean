-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_univ_conj_stable
-- name    : GroundTheory.Automorphic.ContragredientTranspose.univ_conj_stable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:57.275361+00:00
-- url     : https://prove2.me/theorems/b0eef339-6cee-45a3-af11-e8ad906b7954
-- title:
--   Contragredient Transpose: univ conj stable
-- statement:
--   The Contragredient Transpose construction uses the univ conj stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L392-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L392-L393

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

theorem GroundTheory.Automorphic.ContragredientTranspose.univ_conj_stable : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ (univ : Set (GL (Fin n) F)),
    h • x ∈ (univ : Set (GL (Fin n) F)) := by sorry
