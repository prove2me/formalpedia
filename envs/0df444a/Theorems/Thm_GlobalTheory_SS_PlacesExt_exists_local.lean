-- Prove2me | Theorems.Thm_GlobalTheory_SS_PlacesExt_exists_local
-- name    : GlobalTheory.SS.PlacesExt.exists_local
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:30.436257+00:00
-- url     : https://prove2.me/theorems/f2f8e600-b833-40bc-97bc-6a3a5b0bc25b
-- title:
--   Places Ext: exists local
-- statement:
--   The Places Ext construction uses the exists local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesFunctionField.lean#L83-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesFunctionField.lean#L83-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
variable {k F L : Type} [Field k] [Field F] [Algebra k F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] (Pl : Places k F)
variable (L)

theorem GlobalTheory.SS.PlacesExt.exists_local (i : Pl.I) [IsDiscreteValuationRing (Pl.O i)] :
    ∃ (J : Type) (_ : Finite J) (O' : J → ValuationSubring L) (w : J → Lˣ → ℤ),
      (∀ j x y, w j (x * y) = w j x + w j y) ∧ (∀ j (x : Lˣ), (x : L) ∈ O' j ↔ 0 ≤ w j x) ∧
      (∀ y : L, (∀ j, y ∈ O' j) ↔ IsIntegral (Pl.O i) y) ∧
      ∀ y : Lˣ, ∑ᶠ j, w j y = Pl.v i (Units.map (Algebra.norm F) y) := by sorry
