-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_comp_transposeGL_mem_relT_univ
-- name    : GroundTheory.Automorphic.ContragredientTranspose.comp_transposeGL_mem_relT_univ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:57:21.05591+00:00
-- url     : https://prove2.me/theorems/1483e0d4-f57d-43b7-aa66-5511ea8ff835
-- title:
--   Contragredient Transpose: comp transpose GL mem rel T univ
-- statement:
--   The Contragredient Transpose construction uses the comp transpose GL mem rel T univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L440-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L440-L466

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
omit [IsTopologicalRing F]

theorem GroundTheory.Automorphic.ContragredientTranspose.comp_transposeGL_mem_relT_univ {f : GL (Fin n) F → ℂ}
    (hf : f ∈ relT (univ : Set (GL (Fin n) F))) :
    (fun x => f (transposeGL x)) ∈ relT (univ : Set (GL (Fin n) F)) := by sorry
