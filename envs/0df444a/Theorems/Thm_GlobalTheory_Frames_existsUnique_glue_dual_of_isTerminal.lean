-- Prove2me | Theorems.Thm_GlobalTheory_Frames_existsUnique_glue_dual_of_isTerminal
-- name    : GlobalTheory.Frames.existsUnique_glue_dual_of_isTerminal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:13.686599+00:00
-- url     : https://prove2.me/theorems/e3f6e844-c7fa-4e40-9940-7f427f6c8419
-- title:
--   Frames: exists Unique glue dual of is Terminal
-- statement:
--   The Frames construction uses the exists Unique glue dual of is Terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueDual.lean#L21-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueDual.lean#L21-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
noncomputable section
open GlobalTheory GlobalTheory.Frames

theorem GlobalTheory.Frames.existsUnique_glue_dual_of_isTerminal {R : Type} [CommRing R] (hR : IsTerminal (Sp R)) {S : Type} [CommRing S]
    [Algebra R S] (Y : Scheme.{0}) {κ : Type} (h : κ → S) (hs : Ideal.span (Set.range h) = ⊤)
    (w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y)
    (hw : ∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j))
      (β : Localization.Away (h j) →+* Localization.Away (h i * h j)),
      α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) →
      β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) →
      spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) :
    ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i := by sorry
