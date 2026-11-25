-- Prove2me | Theorems.Thm_GlobalTheory_trdeg_residueField_of_trdeg
-- name    : GlobalTheory.trdeg_residueField_of_trdeg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:54.196052+00:00
-- url     : https://prove2.me/theorems/890ad78b-83ac-4df2-a8f8-84bf16a308fa
-- title:
--   Global Theory: trdeg residue Field of trdeg
-- statement:
--   The Global Theory construction uses the trdeg residue Field of trdeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L561-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L561-L596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
variable (F : Type*) [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
  [IsScalarTower K V F]
variable (V)

theorem GlobalTheory.trdeg_residueField_of_trdeg {n : ℕ} (hn : Algebra.trdeg K F = n) :
    Algebra.trdeg K (ResidueField V) = (n - 1 : ℕ) := by sorry
