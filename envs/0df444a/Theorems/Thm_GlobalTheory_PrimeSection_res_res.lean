-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_res_res
-- name    : GlobalTheory.PrimeSection.res_res
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:32.002579+00:00
-- url     : https://prove2.me/theorems/86da1fc5-a657-4d04-886f-9c2cc362c4d7
-- title:
--   Prime Section: res res
-- statement:
--   The Prime Section construction uses the res res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L13-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection

theorem GlobalTheory.PrimeSection.res_res {X : Scheme.{u}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE h').op s) =
      X.presheaf.map (homOfLE (h.trans h')).op s := by sorry
