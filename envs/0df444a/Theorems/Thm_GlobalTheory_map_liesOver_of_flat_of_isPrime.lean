-- Prove2me | Theorems.Thm_GlobalTheory_map_liesOver_of_flat_of_isPrime
-- name    : GlobalTheory.map_liesOver_of_flat_of_isPrime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:09:35.655221+00:00
-- url     : https://prove2.me/theorems/5281a5f2-fec4-4251-8b9d-39f4f043e35e
-- title:
--   Global Theory: map lies Over of flat of is Prime
-- statement:
--   The Global Theory construction uses the map lies Over of flat of is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingExistsAssociatedOfSumEqZero.lean#L120-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingExistsAssociatedOfSumEqZero.lean#L120-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
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

theorem GlobalTheory.map_liesOver_of_flat_of_isPrime {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (p : Ideal A) [p.IsPrime] [(p.map (algebraMap A B)).IsPrime] :
    (p.map (algebraMap A B)).LiesOver p := by sorry
