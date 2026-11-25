-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_mem_relT_univ
-- name    : GroundTheory.Automorphic.ContragredientTranspose.mem_relT_univ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:56:05.556467+00:00
-- url     : https://prove2.me/theorems/82ba7c96-b285-522a-998d-2a3410544708
-- title:
--   Contragredient Transpose: mem rel T univ
-- statement:
--   The Contragredient Transpose construction uses the mem rel T univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L653-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L653-L727

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.mem_relT_univ {g : GL (Fin n) F → ℂ}
    (hg : g ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    g ∈ relT (univ : Set (GL (Fin n) F)) := by sorry
