-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distribution_transpose_invariant
-- name    : GroundTheory.Automorphic.ContragredientTranspose.distribution_transpose_invariant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:03.548855+00:00
-- url     : https://prove2.me/theorems/950a4ce1-4077-58d4-8e61-c02cabcfeb37
-- title:
--   Contragredient Transpose: distribution transpose invariant
-- statement:
--   The Contragredient Transpose construction uses the distribution transpose invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L729-L778
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L729-L778

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

theorem GroundTheory.Automorphic.ContragredientTranspose.distribution_transpose_invariant
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ))
    (hD : ∀ (g : GL (Fin n) F) (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ),
      D (biTranslL g g f) = D f)
    (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    D (compHomeoL transposeHomeo f) = D f := by sorry
