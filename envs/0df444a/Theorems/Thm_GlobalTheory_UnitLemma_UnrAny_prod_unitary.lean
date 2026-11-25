-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrAny_prod_unitary
-- name    : GlobalTheory.UnitLemma.UnrAny.prod_unitary
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:19:44.056019+00:00
-- url     : https://prove2.me/theorems/9ab8db7e-47a1-43e5-a711-70d0ec85aaed
-- title:
--   Unr Any: prod unitary
-- statement:
--   The Unr Any construction uses the prod unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaLocalAnyResidueCharOfLieAlgebra.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaLocalAnyResidueCharOfLieAlgebra.lean#L38-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedBaseChangeLatticeCountEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyOverExtIntegralReductionPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardResidueFieldLocalOrderUnitaryProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnramifiedEmbeddingOfInvolutionAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrAny
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
variable {K K' : UQ}

theorem GlobalTheory.UnitLemma.UnrAny.prod_unitary (B₁ B₂ : InvAlg K) (hu₁ : B₁.g * B₁.σ B₁.g = 1) (hu₂ : B₂.g * B₂.σ B₂.g = 1) :
    (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 := by sorry
