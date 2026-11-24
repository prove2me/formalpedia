-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_kbInvHomeomorphC_equivariant
-- name    : GroundTheory.Automorphic.kbInvHomeomorphC_equivariant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:40.597545+00:00
-- url     : https://prove2.me/theorems/276a094b-cce6-43a7-b8fb-106c886eb57d
-- title:
--   Automorphic: kb Inv Homeomorph C equivariant
-- statement:
--   The Automorphic construction uses the kb Inv Homeomorph C equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroups.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroups.lean#L66-L76

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroups
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
variable {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem GroundTheory.Automorphic.kbInvHomeomorphC_equivariant (q : unitaryGroup n ℂ × upperPosSubgroup n ℂ) (g : GL n ℂ) :
    kbInvHomeomorphC (Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) = q * kbInvHomeomorphC g := by sorry
