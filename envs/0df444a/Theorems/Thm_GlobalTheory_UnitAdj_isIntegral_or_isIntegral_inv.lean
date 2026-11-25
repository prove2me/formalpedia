-- Prove2me | Theorems.Thm_GlobalTheory_UnitAdj_isIntegral_or_isIntegral_inv
-- name    : GlobalTheory.UnitAdj.isIntegral_or_isIntegral_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:30.970193+00:00
-- url     : https://prove2.me/theorems/6eeb4fd9-d5d4-42bc-8294-24f7cbdd699c
-- title:
--   Unit Adj: is Integral or is Integral inv
-- statement:
--   The Unit Adj construction uses the is Integral or is Integral inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L13-L22

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.UnitAdj

theorem GlobalTheory.UnitAdj.isIntegral_or_isIntegral_inv {O K L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [Algebra O L]
    [IsScalarTower O K L] [FiniteDimensional K L] (y : L) :
    IsIntegral O y ∨ IsIntegral O y⁻¹ := by sorry
