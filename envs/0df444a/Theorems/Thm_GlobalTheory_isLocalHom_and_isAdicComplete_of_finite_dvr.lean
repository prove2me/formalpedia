-- Prove2me | Theorems.Thm_GlobalTheory_isLocalHom_and_isAdicComplete_of_finite_dvr
-- name    : GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:48.117992+00:00
-- url     : https://prove2.me/theorems/3f08dbf6-1f3a-5c3d-9f65-f84d8008e16b
-- title:
--   Global Theory: is Local Hom and is Adic Complete of finite dvr
-- statement:
--   The Global Theory construction uses the is Local Hom and is Adic Complete of finite dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsLocalHomAndIsAdicCompleteOfFiniteDvr.lean#L43-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsLocalHomAndIsAdicCompleteOfFiniteDvr.lean#L43-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsLocalHomAndIsAdicCompleteOfFiniteDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr :
    ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CommRing V'] [IsDomain V']
      [IsDiscreteValuationRing V'] [Algebra V V'], Module.Finite V V' →
      Function.Injective (algebraMap V V') →
      IsLocalHom (algebraMap V V') ∧ IsAdicComplete (IsLocalRing.maximalIdeal V') V' := by sorry
