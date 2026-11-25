-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_symm_conj_transposeGL
-- name    : GroundTheory.Automorphic.ContragredientTranspose.exists_symm_conj_transposeGL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:25.858799+00:00
-- url     : https://prove2.me/theorems/3b08e3b4-cf3f-51b5-b181-2d7919fd67b8
-- title:
--   Contragredient Transpose: exists symm conj transpose GL
-- statement:
--   The Contragredient Transpose construction uses the exists symm conj transpose GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L477-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L477-L482

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
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.ContragredientTranspose.exists_symm_conj_transposeGL (x : GL (Fin n) F) :
    ∃ S : GL (Fin n) F, transposeGL S = S ∧ S * x * S⁻¹ = transposeGL x := by sorry
