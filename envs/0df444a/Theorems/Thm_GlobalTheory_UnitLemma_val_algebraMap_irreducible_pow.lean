-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_val_algebraMap_irreducible_pow
-- name    : GlobalTheory.UnitLemma.val_algebraMap_irreducible_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:38:01.287097+00:00
-- url     : https://prove2.me/theorems/8d9bdea2-4e0d-40d4-a418-2947d8d4c8f7
-- title:
--   Unit Lemma: val algebra Map irreducible pow
-- statement:
--   The Unit Lemma construction uses the val algebra Map irreducible pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuation.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuation.lean#L24-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.val_algebraMap_irreducible_pow (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E] {s : O} (hs : Irreducible s) (n : ℕ) :
    val O (algebraMap O E (s ^ n)) = n := by sorry
