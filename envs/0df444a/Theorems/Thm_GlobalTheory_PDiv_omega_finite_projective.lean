-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_omega_finite_projective
-- name    : GlobalTheory.PDiv.omega_finite_projective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:29.261266+00:00
-- url     : https://prove2.me/theorems/37d4efb4-a411-49c7-afa1-6edab7f762d1
-- title:
--   PDiv: omega finite projective
-- statement:
--   The PDiv construction uses the omega finite projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowEqOfIntegers.lean#L24-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowEqOfIntegers.lean#L24-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulPMemSqCounitKerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgHomCotangentPullbackInjectiveOfSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowEqOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PDiv

theorem GlobalTheory.PDiv.omega_finite_projective (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) :
    Module.Finite O G.omega ∧ Module.Projective O G.omega := by sorry
