-- Prove2me | Theorems.Thm_GlobalTheory_KSp_blocks_of_weyl_mul_eq
-- name    : GlobalTheory.KSp.blocks_of_weyl_mul_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:01.069065+00:00
-- url     : https://prove2.me/theorems/8b1478c8-9b08-4415-b3db-a682ad81eaa2
-- title:
--   KSp: blocks of weyl mul eq
-- statement:
--   The KSp construction uses the blocks of weyl mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierIntertwinesSiegelLeviOperator.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierIntertwinesSiegelLeviOperator.lean#L16-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitUnitarySiegelParabolicBlockRelationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapTwoSidedMulHaarMatrixQuadraticExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesSiegelLeviOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp

theorem GlobalTheory.KSp.blocks_of_weyl_mul_eq {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] {p q : UG c (stdJ ν E)} (hp : p ∈ sieg c ν) (hq : q ∈ sieg c ν)
    (h : weyl c ν * p = q * weyl c ν) :
    (mat c p).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₁ = (mat c p).toBlocks₂₂ := by sorry
