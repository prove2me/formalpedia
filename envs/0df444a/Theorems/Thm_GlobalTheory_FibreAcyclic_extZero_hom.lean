-- Prove2me | Theorems.Thm_GlobalTheory_FibreAcyclic_extZero_hom
-- name    : GlobalTheory.FibreAcyclic.extZero_hom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:29.522478+00:00
-- url     : https://prove2.me/theorems/e53b2acd-5a3e-469b-9d34-6c44e1ed228a
-- title:
--   Fibre Acyclic: ext Zero hom
-- statement:
--   The Fibre Acyclic construction uses the ext Zero hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L13-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]

theorem GlobalTheory.FibreAcyclic.extZero_hom (M : Type) [AddCommGroup M] [Module R M] (n : ℕ) (h : ExtZero (R := R) M n)
    (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F] :
    ExtZero (R := R) (F →ₗ[R] M) n := by sorry
