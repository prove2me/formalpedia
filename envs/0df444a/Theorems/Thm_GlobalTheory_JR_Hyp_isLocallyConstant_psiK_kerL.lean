-- Prove2me | Theorems.Thm_GlobalTheory_JR_Hyp_isLocallyConstant_psiK_kerL
-- name    : GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:38.767957+00:00
-- url     : https://prove2.me/theorems/e766b2b1-b65c-4b5c-86e1-9a0b29621a69
-- title:
--   Hyp: is Locally Constant psi K ker L
-- statement:
--   The Hyp construction uses the is Locally Constant psi K ker L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantEtaleTraceAddCharHermitianKerne.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantEtaleTraceAddCharHermitianKerne.lean#L29-L38

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerne
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp

theorem GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by sorry
