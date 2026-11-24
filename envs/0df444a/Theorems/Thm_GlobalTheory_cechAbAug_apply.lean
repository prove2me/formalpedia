-- Prove2me | Theorems.Thm_GlobalTheory_cechAbAug_apply
-- name    : GlobalTheory.cechAbAug_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:42.093857+00:00
-- url     : https://prove2.me/theorems/27b54965-0f58-41e8-8d4d-cdf68b99d74d
-- title:
--   Global Theory: cech Ab Aug apply
-- statement:
--   The Global Theory construction uses the cech Ab Aug apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PresheafCubeExactAtSuccOfSurjective.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PresheafCubeExactAtSuccOfSurjective.lean#L32-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : TopCat.{w}} {ι : Type}

theorem GlobalTheory.cechAbAug_apply (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) (V : Opens T) (U : ι → Opens T)
    (x : P.obj (op V)) (s : {s : Finset ι // s.card = 1}) :
    cechAbAug P V U x s = P.map (homOfLE (cechOpen_le V U s.1)).op x := by sorry

attribute [defeq] GlobalTheory.cechAbAug_apply
