-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_repr_prod_self
-- name    : GlobalTheory.Lyndon.repr_prod_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:07.421155+00:00
-- url     : https://prove2.me/theorems/b5342a4e-cb7f-4946-8bbf-34923e6a0434
-- title:
--   Lyndon: repr prod self
-- statement:
--   The Lyndon construction uses the repr prod self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L554-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L554-L557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
open ShuffleAlgebra
variable (K : Type) [Field K]

theorem GlobalTheory.Lyndon.repr_prod_self [CharZero K] (L : List (List A)) :
    (wordBasis K A).repr (L.map (word K)).prod L.flatten ≠ 0 := by sorry
