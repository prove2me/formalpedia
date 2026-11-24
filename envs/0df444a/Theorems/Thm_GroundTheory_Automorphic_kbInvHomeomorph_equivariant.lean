-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_kbInvHomeomorph_equivariant
-- name    : GroundTheory.Automorphic.kbInvHomeomorph_equivariant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:40.343483+00:00
-- url     : https://prove2.me/theorems/b6879d10-db6f-45ab-8968-262ca706ad65
-- title:
--   Automorphic: kb Inv Homeomorph equivariant
-- statement:
--   The Automorphic construction uses the kb Inv Homeomorph equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawaHaar.lean#L151-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawaHaar.lean#L151-L161

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix Set
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem GroundTheory.Automorphic.kbInvHomeomorph_equivariant (q : unitaryGroup n ℝ × upperPosSubgroup n ℝ) (g : GL n ℝ) :
    kbInvHomeomorph (Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) = q * kbInvHomeomorph g := by sorry
