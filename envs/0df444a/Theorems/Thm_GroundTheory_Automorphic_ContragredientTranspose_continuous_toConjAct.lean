-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_continuous_toConjAct
-- name    : GroundTheory.Automorphic.ContragredientTranspose.continuous_toConjAct
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:55:27.150847+00:00
-- url     : https://prove2.me/theorems/9b8d6284-3e82-555c-a9b8-8da1411a8861
-- title:
--   Contragredient Transpose: continuous to Conj Act
-- statement:
--   The Contragredient Transpose construction uses the continuous to Conj Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L20-L20

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
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem GroundTheory.Automorphic.ContragredientTranspose.continuous_toConjAct : Continuous (ConjAct.toConjAct : G → ConjAct G) := by sorry
