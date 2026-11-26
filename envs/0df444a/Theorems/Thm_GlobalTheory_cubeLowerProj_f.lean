-- Prove2me | Theorems.Thm_GlobalTheory_cubeLowerProj_f
-- name    : GlobalTheory.cubeLowerProj_f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:22.129227+00:00
-- url     : https://prove2.me/theorems/3ed3b313-5b19-50da-91cd-471393ce9005
-- title:
--   Global Theory: cube Lower Proj f
-- statement:
--   The Global Theory construction uses the cube Lower Proj f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L459-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L459-L460

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

theorem GlobalTheory.cubeLowerProj_f (A : Cube.{v} ι R) (p : ℕ) :
    (cubeLowerProj e A).f p = ModuleCat.ofHom (Cube.termLower e A p) := by sorry
