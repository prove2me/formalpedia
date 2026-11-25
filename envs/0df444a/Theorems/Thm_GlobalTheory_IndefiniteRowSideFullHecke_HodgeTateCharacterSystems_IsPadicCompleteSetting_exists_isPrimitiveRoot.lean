-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgeTateCharacterSystems_IsPadicCompleteSetting_exists_isPrimitiveRoot
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.IsPadicCompleteSetting.exists_isPrimitiveRoot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:58.973959+00:00
-- url     : https://prove2.me/theorems/603e9fe3-ec46-5664-8bcd-d2fa874ba2ff
-- title:
--   Is Padic Complete Setting: exists is Primitive Root
-- statement:
--   The Is Padic Complete Setting construction uses the exists is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HodgeTateCharacterSystems.lean#L275-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HodgeTateCharacterSystems.lean#L275-L290

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
noncomputable section
variable {C : Type u} [Field C]

theorem GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.IsPadicCompleteSetting.exists_isPrimitiveRoot {O : ValuationSubring C} {p : ℕ}
    (h : IsPadicCompleteSetting O p) : ∃ ζ : O, IsPrimitiveRoot ζ p := by sorry
