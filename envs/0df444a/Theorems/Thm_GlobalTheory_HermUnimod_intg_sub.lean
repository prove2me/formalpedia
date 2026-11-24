-- Prove2me | Theorems.Thm_GlobalTheory_HermUnimod_intg_sub
-- name    : GlobalTheory.HermUnimod.intg_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:07.731979+00:00
-- url     : https://prove2.me/theorems/a991ceba-7490-49a5-ba60-bd0aaccfb6e5
-- title:
--   Herm Unimod: intg sub
-- statement:
--   The Herm Unimod construction uses the intg sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L69-L72

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
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem GlobalTheory.HermUnimod.intg_sub {n m : Type} {A B : Matrix n m E} (hA : Intg A) (hB : Intg B) : Intg (A - B) := by sorry
