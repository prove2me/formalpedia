-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_univJ_dim_unique
-- name    : GlobalTheory.ChartCmp.univJ_dim_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:00.522747+00:00
-- url     : https://prove2.me/theorems/24d3178b-40ea-5667-bcd6-245356cd875b
-- title:
--   Chart Cmp: univ J dim unique
-- statement:
--   The Chart Cmp construction uses the univ J dim unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L95-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem GlobalTheory.ChartCmp.univJ_dim_unique : ∀ (V : Type) [CommRing V] [Nontrivial V] (G : Over (Sp V)) [GrpObj G] (d d' : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d') x' → d = d' := by sorry
