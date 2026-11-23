-- Prove2me | Theorems.Thm_GlobalTheory_T_isLocallyConstant_etaleTraceAddChar_hermitianKernel
-- name    : GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:51.865402+00:00
-- url     : https://prove2.me/theorems/9077ca46-e2b1-49e9-a861-9dd567eddf92
-- title:
--   T: is Locally Constant etale Trace Add Char hermitian Kernel
-- statement:
--   The T construction uses the is Locally Constant etale Trace Add Char hermitian Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by sorry
