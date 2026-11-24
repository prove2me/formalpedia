-- Prove2me | Theorems.Thm_GlobalTheory_isIso_cubeLowerProj
-- name    : GlobalTheory.isIso_cubeLowerProj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:07.856782+00:00
-- url     : https://prove2.me/theorems/097a168d-a0a3-4bb2-aeaf-5838813ee4b8
-- title:
--   Global Theory: is Iso cube Lower Proj
-- statement:
--   The Global Theory construction uses the is Iso cube Lower Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L467-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L467-L484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}

theorem GlobalTheory.isIso_cubeLowerProj (he : Function.Surjective e) (A : Cube.{v} ι R) :
    IsIso (cubeLowerProj e A) := by sorry
