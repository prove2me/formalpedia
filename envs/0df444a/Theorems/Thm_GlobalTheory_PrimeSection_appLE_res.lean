-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_appLE_res
-- name    : GlobalTheory.PrimeSection.appLE_res
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:44:40.148239+00:00
-- url     : https://prove2.me/theorems/1419ebd5-81b5-409e-bb75-f6b616ccec5e
-- title:
--   Prime Section: app LE res
-- statement:
--   The Prime Section construction uses the app LE res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L17-L21

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

theorem GlobalTheory.PrimeSection.appLE_res {X Y : Scheme.{u}} (j : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U') (h' : U' ≤ U) (s : Γ(X, U)) :
    j.appLE U' W h (X.presheaf.map (homOfLE h').op s) =
      j.appLE U W (h.trans (j.preimage_mono h')) s := by sorry
