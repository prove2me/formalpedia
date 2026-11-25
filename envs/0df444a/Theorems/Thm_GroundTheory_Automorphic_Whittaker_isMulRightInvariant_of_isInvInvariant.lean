-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isMulRightInvariant_of_isInvInvariant
-- name    : GroundTheory.Automorphic.Whittaker.isMulRightInvariant_of_isInvInvariant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:50.981831+00:00
-- url     : https://prove2.me/theorems/88c49018-a064-4a23-a0de-40bd4f5cc69d
-- title:
--   Whittaker: is Mul Right Invariant of is Inv Invariant
-- statement:
--   The Whittaker construction uses the is Mul Right Invariant of is Inv Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L727-L731
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L727-L731

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

theorem GroundTheory.Automorphic.Whittaker.isMulRightInvariant_of_isInvInvariant (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsInvInvariant] : μ.IsMulRightInvariant := by sorry
