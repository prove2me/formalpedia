-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_eq_zero_of_extZero
-- name    : GlobalTheory.DualCokernel.eq_zero_of_extZero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:01.626101+00:00
-- url     : https://prove2.me/theorems/59b84583-0e07-4399-b573-474941db1a47
-- title:
--   Dual Cokernel: eq zero of ext Zero
-- statement:
--   The Dual Cokernel construction uses the eq zero of ext Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L103-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L103-L118

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
variable [IsLocalRing R]
variable [IsNoetherianRing R]

theorem GlobalTheory.DualCokernel.eq_zero_of_extZero {M : Type} [AddCommGroup M] [Module R M] (h : ExtZero (R := R) M 0)
    (x : M) (hx : ∀ p : Ideal R, p.IsPrime → p ≠ maximalIdeal R → ∃ s, s ∉ p ∧ s • x = 0) :
    x = 0 := by sorry
