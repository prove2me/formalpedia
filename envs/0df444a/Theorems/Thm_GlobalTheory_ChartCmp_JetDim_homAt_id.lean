-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_JetDim_homAt_id
-- name    : GlobalTheory.ChartCmp.JetDim.homAt_id
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:35:54.432466+00:00
-- url     : https://prove2.me/theorems/c2de4c9e-db00-5532-8e76-3bcbbc70fdff
-- title:
--   Jet Dim: hom At id
-- statement:
--   The Jet Dim construction uses the hom At id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L74-L76

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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JetDim
variable {V : Type} [CommRing V]

theorem GlobalTheory.ChartCmp.JetDim.homAt_id {A : Type} [CommRing A] [Algebra V A] : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V A) = 𝟙 _ := by sorry
