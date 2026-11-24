-- Prove2me | Theorems.Thm_GlobalTheory_nontrivial_tensor_of_mem_support
-- name    : GlobalTheory.nontrivial_tensor_of_mem_support
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:34.798447+00:00
-- url     : https://prove2.me/theorems/7f7603b6-3b94-488d-ae2e-e2e537f6369f
-- title:
--   Global Theory: nontrivial tensor of mem support
-- statement:
--   The Global Theory construction uses the nontrivial tensor of mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AlgebraMapSurjectiveOfUnramifiedOfUniquePoint.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AlgebraMapSurjectiveOfUnramifiedOfUniquePoint.lean#L30-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.nontrivial_tensor_of_mem_support (R C K : Type) [CommRing R] [AddCommGroup C] [Module R C]
    [Module.Finite R C] [Field K] [Algebra R K] (p : PrimeSpectrum R)
    (hp : RingHom.ker (algebraMap R K) = p.asIdeal) (h : p ∈ Module.support R C) :
    Nontrivial (K ⊗[R] C) := by sorry
