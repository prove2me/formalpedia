-- Prove2me | Theorems.Thm_GlobalTheory_SS_PlacesExt_isAlgebraic_of_forall
-- name    : GlobalTheory.SS.PlacesExt.isAlgebraic_of_forall
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:11.602871+00:00
-- url     : https://prove2.me/theorems/b7b88052-a1e1-4354-a183-71dd7a211712
-- title:
--   Places Ext: is Algebraic of forall
-- statement:
--   The Places Ext construction uses the is Algebraic of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesFunctionField.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesFunctionField.lean#L172-L184

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

theorem GlobalTheory.SS.PlacesExt.isAlgebraic_of_forall [Algebra k L] [IsScalarTower k F L]
    (hc : ∀ c : F, (∀ i, c ∈ Pl.O i) → c ∈ Set.range (algebraMap k F)) (y : L)
    (hy : ∀ i, IsIntegral (Pl.O i) y) : IsAlgebraic k y := by sorry
