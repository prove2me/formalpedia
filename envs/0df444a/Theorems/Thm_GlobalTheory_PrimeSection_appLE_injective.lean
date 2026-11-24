-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_appLE_injective
-- name    : GlobalTheory.PrimeSection.appLE_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:42:56.347224+00:00
-- url     : https://prove2.me/theorems/16aa8b3f-fa3e-4eb2-b3dd-96bcec1a1dcb
-- title:
--   Prime Section: app LE injective
-- statement:
--   The Prime Section construction uses the app LE injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L43-L51

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

theorem GlobalTheory.PrimeSection.appLE_injective {X Y : Scheme.{u}} [IsIntegral X] (j : Y ⟶ X) [IsOpenImmersion j]
    [Nonempty Y] {U : X.Opens} {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Injective (j.appLE U W h.le) := by sorry
