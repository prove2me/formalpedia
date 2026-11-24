-- Prove2me | Theorems.Thm_GlobalTheory_HermUnimod_intg_mul
-- name    : GlobalTheory.HermUnimod.intg_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:05.676385+00:00
-- url     : https://prove2.me/theorems/71aa7f3f-005d-41e0-810b-a066c0e20ba6
-- title:
--   Herm Unimod: intg mul
-- statement:
--   The Herm Unimod construction uses the intg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L27-L33

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E]

theorem GlobalTheory.HermUnimod.intg_mul [IsUltrametricDist E] {l n m : Type} [Fintype n] {A : Matrix l n E} {B : Matrix n m E} (hA : Intg A)
    (hB : Intg B) : Intg (A * B) := by sorry
