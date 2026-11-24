-- Prove2me | Theorems.Thm_GlobalTheory_KeyPow_chiAt_iff_thetaLaw
-- name    : GlobalTheory.KeyPow.chiAt_iff_thetaLaw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:32.427821+00:00
-- url     : https://prove2.me/theorems/fc4247e2-3354-4281-a4dd-d3c5a6018751
-- title:
--   Key Pow: chi At iff theta Law
-- statement:
--   The Key Pow construction uses the chi At iff theta Law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/KeyRuleOneOfKeyFormula.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/KeyRuleOneOfKeyFormula.lean#L129-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
open ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.KeyPow.chiAt_iff_thetaLaw (g : ℕ) (sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ChiAt g sp ↔ ∀ n n' : Fin g → ℤ, ∃ k k' : Fin g → ℤ,
      (∀ i, k i = 0 ∨ k i = 1) ∧ (∀ i, k' i = 0 ∨ k' i = 1) ∧ ThetaLaw g sp n n' k k' := by sorry
