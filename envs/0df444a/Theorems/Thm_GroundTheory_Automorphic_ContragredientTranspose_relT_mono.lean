-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_relT_mono
-- name    : GroundTheory.Automorphic.ContragredientTranspose.relT_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:53.489357+00:00
-- url     : https://prove2.me/theorems/6947fb15-f448-43a0-9389-1f07471076f2
-- title:
--   Contragredient Transpose: rel T mono
-- statement:
--   The Contragredient Transpose construction uses the rel T mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L211-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L211-L216

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

theorem GroundTheory.Automorphic.ContragredientTranspose.relT_mono {U V : Set (GL (Fin n) F)} (hUV : U ⊆ V) : relT U ≤ relT V := by sorry
