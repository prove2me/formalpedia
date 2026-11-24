-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_appLE_appLE
-- name    : GlobalTheory.PrimeSection.appLE_appLE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:46.21938+00:00
-- url     : https://prove2.me/theorems/695ed9d9-3f8c-42f2-8b31-be661e724db0
-- title:
--   Prime Section: app LE app LE
-- statement:
--   The Prime Section construction uses the app LE app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L23-L28

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

theorem GlobalTheory.PrimeSection.appLE_appLE {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) {k : Z ⟶ X} (hk : i ≫ j = k)
    {U : X.Opens} {W : Y.Opens} {A : Z.Opens} (h : W ≤ j ⁻¹ᵁ U) (h' : A ≤ i ⁻¹ᵁ W)
    (h'' : A ≤ k ⁻¹ᵁ U) (s : Γ(X, U)) :
    i.appLE W A h' (j.appLE U W h s) = k.appLE U A h'' s := by sorry
