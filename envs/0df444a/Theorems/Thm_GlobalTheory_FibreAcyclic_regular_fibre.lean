-- Prove2me | Theorems.Thm_GlobalTheory_FibreAcyclic_regular_fibre
-- name    : GlobalTheory.FibreAcyclic.regular_fibre
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:41.859298+00:00
-- url     : https://prove2.me/theorems/5668455c-353f-43b1-a080-574e84f4557d
-- title:
--   Fibre Acyclic: regular fibre
-- statement:
--   The Fibre Acyclic construction uses the regular fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L207-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L207-L258

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
omit [IsLocalRing R]

theorem GlobalTheory.FibreAcyclic.regular_fibre {A T : Type} [CommRing A] [IsLocalRing A] [CommRing T] [Algebra A T] (g : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g A T] (q : Ideal T) [hq : q.IsMaximal]
    (hm : (maximalIdeal A).map (algebraMap A T) ≤ q) [Algebra T R] [IsLocalization.AtPrime R q] [Algebra A R]
    [IsScalarTower A T R] :
    IsRegularLocalRing (R ⧸ (maximalIdeal A).map (algebraMap A R)) ∧
      (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by sorry
