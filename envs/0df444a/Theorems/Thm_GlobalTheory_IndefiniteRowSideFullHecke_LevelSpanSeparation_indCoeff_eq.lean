-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelSpanSeparation_indCoeff_eq
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.indCoeff_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:14:55.410483+00:00
-- url     : https://prove2.me/theorems/039d1e43-9a3f-4871-8429-e36c76d09065
-- title:
--   Level Span Separation: ind Coeff eq
-- statement:
--   The Level Span Separation construction uses the ind Coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LevelIndexFourierCharacter.lean#L210-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LevelIndexFourierCharacter.lean#L210-L215

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable (D : Datum H) (l : Level H)
variable {l}
variable {D}

theorem GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.indCoeff_eq (c : Coeff l) {n : ℕ} (x₀ : Fin n → ConjCl D l) (t : Fin n → NamedCl D l) :
    indCoeff c x₀ t = (Nat.card (Fin n → NamedCl D l) : c.F)⁻¹ * (zetaM c ^ (pairing D l x₀ t).val)⁻¹ := by sorry
