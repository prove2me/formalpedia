-- Prove2me | Theorems.Thm_GlobalTheory_FibreAcyclic_extZero_quotient
-- name    : GlobalTheory.FibreAcyclic.extZero_quotient
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:05.548828+00:00
-- url     : https://prove2.me/theorems/8f60c47a-bb97-4ac5-9528-3ecb6045470f
-- title:
--   Fibre Acyclic: ext Zero quotient
-- statement:
--   The Fibre Acyclic construction uses the ext Zero quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L30-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L30-L55

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

theorem GlobalTheory.FibreAcyclic.extZero_quotient [IsNoetherianRing R] (N : Ideal R) [IsRegularLocalRing (R ⧸ N)] (g : ℕ)
    (hg : (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ N)) (j : ℕ) (hj : j < g) : ExtZero (R := R) (R ⧸ N) j := by sorry
