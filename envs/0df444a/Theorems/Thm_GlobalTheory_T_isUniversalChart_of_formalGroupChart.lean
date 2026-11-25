-- Prove2me | Theorems.Thm_GlobalTheory_T_isUniversalChart_of_formalGroupChart
-- name    : GlobalTheory.T.isUniversalChart_of_formalGroupChart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:06.318817+00:00
-- url     : https://prove2.me/theorems/eadf1229-4e0d-4303-91df-020e41f940e3
-- title:
--   T: is Universal Chart of formal Group Chart
-- statement:
--   The T construction uses the is Universal Chart of formal Group Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChartStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChartStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isUniversalChart_of_formalGroupChart : ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 ∧ ∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left := by sorry
