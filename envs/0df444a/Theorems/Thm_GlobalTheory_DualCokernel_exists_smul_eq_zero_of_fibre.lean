-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_exists_smul_eq_zero_of_fibre
-- name    : GlobalTheory.DualCokernel.exists_smul_eq_zero_of_fibre
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:39.949289+00:00
-- url     : https://prove2.me/theorems/f42f38e8-bf95-4fdb-9e15-7ffb7c595cb1
-- title:
--   Dual Cokernel: exists smul eq zero of fibre
-- statement:
--   The Dual Cokernel construction uses the exists smul eq zero of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]

theorem GlobalTheory.DualCokernel.exists_smul_eq_zero_of_fibre (p : Ideal R) [hp : p.IsPrime] (N : Type) [AddCommGroup N]
    [Module R N] [Module.Finite R N] (h : Subsingleton (p.ResidueField ⊗[R] N)) :
    ∃ s, s ∉ p ∧ ∀ x : N, s • x = 0 := by sorry
