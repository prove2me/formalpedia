-- Prove2me | Theorems.Thm_GlobalTheory_UnitAdj_isIntegral_of_residues
-- name    : GlobalTheory.UnitAdj.isIntegral_of_residues
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:21.512124+00:00
-- url     : https://prove2.me/theorems/4226a1fb-a62c-4f3a-b7ea-ca94712990cd
-- title:
--   Unit Adj: is Integral of residues
-- statement:
--   The Unit Adj construction uses the is Integral of residues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L40-L49

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
variable {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem GlobalTheory.UnitAdj.isIntegral_of_residues {O : Type} [CommRing O] [Algebra O A] {y : A}
    (h : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal y)) :
    IsIntegral O y := by sorry
