-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_appLE_bijective
-- name    : GlobalTheory.PrimeSection.appLE_bijective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:18.532843+00:00
-- url     : https://prove2.me/theorems/9043f8e1-045e-45c2-9e36-148b3edfef17
-- title:
--   Prime Section: app LE bijective
-- statement:
--   The Prime Section construction uses the app LE bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L30-L36

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

theorem GlobalTheory.PrimeSection.appLE_bijective {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] {U : X.Opens}
    (hU : U ≤ j.opensRange) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Bijective (j.appLE U W h.le) := by sorry
