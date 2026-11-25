-- Prove2me | Theorems.Thm_GlobalTheory_UnitAdj_eq_zero_of_forall_mem
-- name    : GlobalTheory.UnitAdj.eq_zero_of_forall_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:57.926408+00:00
-- url     : https://prove2.me/theorems/180b8c97-b8dc-427b-89b0-9ade5e21937b
-- title:
--   Unit Adj: eq zero of forall mem
-- statement:
--   The Unit Adj construction uses the eq zero of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean#L33-L38

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

theorem GlobalTheory.UnitAdj.eq_zero_of_forall_mem {y : A} (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by sorry
