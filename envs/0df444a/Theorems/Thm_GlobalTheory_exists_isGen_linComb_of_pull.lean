-- Prove2me | Theorems.Thm_GlobalTheory_exists_isGen_linComb_of_pull
-- name    : GlobalTheory.exists_isGen_linComb_of_pull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:01.349732+00:00
-- url     : https://prove2.me/theorems/8443b346-8982-4048-8f02-6bb7bc1fc4b6
-- title:
--   Global Theory: exists is Gen lin Comb of pull
-- statement:
--   The Global Theory construction uses the exists is Gen lin Comb of pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsGenTranslDiffComp.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsGenTranslDiffComp.lean#L15-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsGenTranslDiffComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.exists_isGen_linComb_of_pull {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (f : Z ⟶ Y) (c : LB.Gen ((LB.LinComb L φ ε).pull f))
    (hc : c.IsGen) : ∃ d : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), d.IsGen := by sorry
