-- Prove2me | Theorems.Thm_GlobalTheory_SS_ArcInf_exists_isChart
-- name    : GlobalTheory.SS.ArcInf.exists_isChart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:33:36.193364+00:00
-- url     : https://prove2.me/theorems/500a68a6-114b-449c-a8cd-63abf4e2b658
-- title:
--   Arc Inf: exists is Chart
-- statement:
--   The Arc Inf construction uses the exists is Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAffineUnitChartSmoothGroupScheme.lean#L16-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAffineUnitChartSmoothGroupScheme.lean#L16-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAffineUnitChartSmoothGroupScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf

theorem GlobalTheory.SS.ArcInf.exists_isChart : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by sorry
