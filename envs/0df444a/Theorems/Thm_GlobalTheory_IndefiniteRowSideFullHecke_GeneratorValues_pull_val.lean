-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_pull_val
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.pull_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:13:47.561939+00:00
-- url     : https://prove2.me/theorems/853e6196-77e1-415a-b315-6111d5adf063
-- title:
--   Generator Values: pull val
-- statement:
--   The Generator Values construction uses the pull val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L53-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.pull_val {X : Scheme.{0}} {S T : CommRingCat.{0}} (φ : S ⟶ T) (c : Spec S ⟶ X)
    (U : X.Opens) (g : Γ(X, U)ˣ) (h : ⊤ ≤ c ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map φ ≫ c) ⁻¹ᵁ U) :
    Units.map (Scheme.ΓSpecIso T).hom.hom.toMonoidHom (res h' (pullU (Spec.map φ ≫ c) U g)) =
      Units.map φ.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso S).hom.hom.toMonoidHom (res h (pullU c U g))) := by sorry
