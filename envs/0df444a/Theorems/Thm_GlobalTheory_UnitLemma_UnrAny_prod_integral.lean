-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrAny_prod_integral
-- name    : GlobalTheory.UnitLemma.UnrAny.prod_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:24:37.395809+00:00
-- url     : https://prove2.me/theorems/d14c7a9b-0ac8-49ba-9bd8-d7304c25466b
-- title:
--   Unr Any: prod integral
-- statement:
--   The Unr Any construction uses the prod integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaLocalAnyResidueCharOfLieAlgebra.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaLocalAnyResidueCharOfLieAlgebra.lean#L42-L54

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

theorem GlobalTheory.UnitLemma.UnrAny.prod_integral (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by sorry
