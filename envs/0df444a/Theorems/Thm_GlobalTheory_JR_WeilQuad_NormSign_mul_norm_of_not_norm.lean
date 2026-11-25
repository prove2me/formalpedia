-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_mul_norm_of_not_norm
-- name    : GlobalTheory.JR.WeilQuad.NormSign.mul_norm_of_not_norm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:20.348791+00:00
-- url     : https://prove2.me/theorems/01c662f1-4dde-43dd-996c-5bea86793751
-- title:
--   Norm Sign: mul norm of not norm
-- statement:
--   The Norm Sign construction uses the mul norm of not norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormGroupSignMulAndNegOne.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormGroupSignMulAndNegOne.lean#L45-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NegOneMemNormOfValuationEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NormSign

theorem GlobalTheory.JR.WeilQuad.NormSign.mul_norm_of_not_norm (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (s t : Kˣ) (hs : ¬ ∃ y : L, Algebra.norm K y = s) (ht : ¬ ∃ y : L, Algebra.norm K y = t) :
    ∃ y : L, Algebra.norm K y = ((s * t : Kˣ) : K) := by sorry
