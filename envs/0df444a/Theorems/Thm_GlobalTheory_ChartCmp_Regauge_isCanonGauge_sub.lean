-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_Regauge_isCanonGauge_sub
-- name    : GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:37:57.57845+00:00
-- url     : https://prove2.me/theorems/1ee7f4be-1a4a-49af-8f5b-8fd018abda9c
-- title:
--   Regauge: is Canon Gauge sub
-- statement:
--   The Regauge construction uses the is Canon Gauge sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsCanonicalGaugeSubBiadditive.lean#L18-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsCanonicalGaugeSubBiadditive.lean#L18-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsCanonicalGaugeSubBiadditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by sorry
