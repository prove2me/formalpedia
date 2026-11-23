-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_kbHomeomorph_apply
-- name    : GroundTheory.Automorphic.kbHomeomorph_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:46.178574+00:00
-- url     : https://prove2.me/theorems/17a764aa-423d-4857-b8d0-457fa0253c72
-- title:
--   Automorphic: kb Homeomorph apply
-- statement:
--   The Automorphic construction uses the kb Homeomorph apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawaHaar.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawaHaar.lean#L98-L99

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
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem GroundTheory.Automorphic.kbHomeomorph_apply (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) :
    kbHomeomorph p = Unitary.toUnits p.1 * p.2 := by sorry
