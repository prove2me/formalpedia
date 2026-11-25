-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_comp_transposeGL_mem
-- name    : GroundTheory.Automorphic.ContragredientTranspose.comp_transposeGL_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:14.333514+00:00
-- url     : https://prove2.me/theorems/b67c3a75-800a-488f-8ba0-4a49b353851f
-- title:
--   Contragredient Transpose: comp transpose GL mem
-- statement:
--   The Contragredient Transpose construction uses the comp transpose GL mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L193-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L193-L197

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

theorem GroundTheory.Automorphic.ContragredientTranspose.comp_transposeGL_mem {U : Set (GL (Fin n) F)}
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) {f : GL (Fin n) F → ℂ} (hf : f ∈ supportedIn U) :
    (fun x => f (transposeGL x)) ∈ supportedIn U := by sorry
