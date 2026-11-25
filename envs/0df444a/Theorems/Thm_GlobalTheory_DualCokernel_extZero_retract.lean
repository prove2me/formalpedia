-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_extZero_retract
-- name    : GlobalTheory.DualCokernel.extZero_retract
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:24.361228+00:00
-- url     : https://prove2.me/theorems/85b8789a-808d-450a-990c-e45726bde016
-- title:
--   Dual Cokernel: ext Zero retract
-- statement:
--   The Dual Cokernel construction uses the ext Zero retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L92-L99

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

theorem GlobalTheory.DualCokernel.extZero_retract {X F : Type} [AddCommGroup X] [Module R X] [AddCommGroup F] [Module R F]
    (f : X →ₗ[R] F) (q : F →ₗ[R] X) (h : q ∘ₗ f = LinearMap.id) (n : ℕ)
    (hF : ExtZero (R := R) F n) : ExtZero (R := R) X n := by sorry
