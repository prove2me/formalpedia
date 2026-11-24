-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_irreducible_algebraMap
-- name    : GlobalTheory.PrimeElement.irreducible_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:41.640391+00:00
-- url     : https://prove2.me/theorems/c7b4e2fa-dce3-4cae-b2d8-b998390df5a8
-- title:
--   Prime Element: irreducible algebra Map
-- statement:
--   The Prime Element construction uses the irreducible algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L56-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]

theorem GlobalTheory.PrimeElement.irreducible_algebraMap [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    Irreducible (algebraMap R S π) := by sorry
