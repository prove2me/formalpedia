-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_tauSpan_le
-- name    : GroundTheory.Automorphic.ContragredientTranspose.tauSpan_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:43.351608+00:00
-- url     : https://prove2.me/theorems/5e582776-7365-4d3c-bb34-40c7de0406f1
-- title:
--   Contragredient Transpose: tau Span le
-- statement:
--   The Contragredient Transpose construction uses the tau Span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L200-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L200-L204

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

theorem GroundTheory.Automorphic.ContragredientTranspose.tauSpan_le {U : Set (GL (Fin n) F)} (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) :
    tauSpan U ≤ supportedIn U := by sorry
