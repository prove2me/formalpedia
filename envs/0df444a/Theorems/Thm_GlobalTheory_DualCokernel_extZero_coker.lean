-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_extZero_coker
-- name    : GlobalTheory.DualCokernel.extZero_coker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:23.316817+00:00
-- url     : https://prove2.me/theorems/705f0742-265f-4845-b257-26b763512df6
-- title:
--   Dual Cokernel: ext Zero coker
-- statement:
--   The Dual Cokernel construction uses the ext Zero coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L81-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L81-L90

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

theorem GlobalTheory.DualCokernel.extZero_coker {X F : Type} [AddCommGroup X] [Module R X] [AddCommGroup F] [Module R F]
    {Y : Type} [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] F) (q : F →ₗ[R] Y) (hf : Injective f)
    (hq : Surjective q) (hex : Exact f q) (n : ℕ) (hX : ExtZero (R := R) X (n + 1))
    (hF : ExtZero (R := R) F n) : ExtZero (R := R) Y n := by sorry
