-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_res_appLE
-- name    : GlobalTheory.PrimeSection.res_appLE
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:10.201026+00:00
-- url     : https://prove2.me/theorems/8a96d94e-2229-4f1c-ba57-434defb91658
-- title:
--   Prime Section: res app LE
-- statement:
--   The Prime Section construction uses the res app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection

theorem GlobalTheory.PrimeSection.res_appLE {X Y : Scheme.{u}} (j : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U) (h' : W' ≤ W) (s : Γ(X, U)) :
    Y.presheaf.map (homOfLE h').op (j.appLE U W h s) = j.appLE U W' (h'.trans h) s := by sorry
