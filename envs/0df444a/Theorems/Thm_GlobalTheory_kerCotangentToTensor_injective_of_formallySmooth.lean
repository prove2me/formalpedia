-- Prove2me | Theorems.Thm_GlobalTheory_kerCotangentToTensor_injective_of_formallySmooth
-- name    : GlobalTheory.kerCotangentToTensor_injective_of_formallySmooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:01.3273+00:00
-- url     : https://prove2.me/theorems/b816ebd6-a78b-4ac0-bfb7-c38d1cca1033
-- title:
--   Global Theory: ker Cotangent To Tensor injective of formally Smooth
-- statement:
--   The Global Theory construction uses the ker Cotangent To Tensor injective of formally Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSqLocalizationOfPderivMem.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSqLocalizationOfPderivMem.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.kerCotangentToTensor_injective_of_formallySmooth (k R F : Type*) [CommRing k] [CommRing R]
    [CommRing F] [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F]
    [Algebra.FormallySmooth k F] (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by sorry
