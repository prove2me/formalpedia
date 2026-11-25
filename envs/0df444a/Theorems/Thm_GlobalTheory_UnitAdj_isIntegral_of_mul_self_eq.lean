-- Prove2me | Theorems.Thm_GlobalTheory_UnitAdj_isIntegral_of_mul_self_eq
-- name    : GlobalTheory.UnitAdj.isIntegral_of_mul_self_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:22.095122+00:00
-- url     : https://prove2.me/theorems/da3852da-9c6d-4ca8-80ca-30eaa7eed9ae
-- title:
--   Unit Adj: is Integral of mul self eq
-- statement:
--   The Unit Adj construction uses the is Integral of mul self eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L24-L27

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

theorem GlobalTheory.UnitAdj.isIntegral_of_mul_self_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {e : A}
    (he : e * e = e) : IsIntegral O e := by sorry
