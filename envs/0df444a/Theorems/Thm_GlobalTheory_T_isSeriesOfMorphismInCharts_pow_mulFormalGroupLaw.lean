-- Prove2me | Theorems.Thm_GlobalTheory_T_isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw
-- name    : GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:40.120449+00:00
-- url     : https://prove2.me/theorems/887fd578-5cb8-4c16-9d72-df10374f6c99
-- title:
--   T: is Series Of Morphism In Charts pow mul Formal Group Law
-- statement:
--   The T construction uses the is Series Of Morphism In Charts pow mul Formal Group Law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement
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

theorem GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by sorry
