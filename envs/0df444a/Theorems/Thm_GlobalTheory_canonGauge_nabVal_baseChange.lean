-- Prove2me | Theorems.Thm_GlobalTheory_canonGauge_nabVal_baseChange
-- name    : GlobalTheory.canonGauge_nabVal_baseChange
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:12:41.834716+00:00
-- url     : https://prove2.me/theorems/92fc6756-7f4f-44f9-88aa-30fd038fcc2c
-- title:
--   Global Theory: canon Gauge nab Val base Change
-- statement:
--   The Global Theory construction uses the canon Gauge nab Val base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeNabValBaseChange.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeNabValBaseChange.lean#L134-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeNabValBaseChange
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory

theorem GlobalTheory.canonGauge_nabVal_baseChange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k k' : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing k'] [Algebra ℚ k'] [Algebra R k'] (β : k →ₐ[R] k') (h : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) ∧ ∀ (w0 : O) (m : ℕ) (f : PS k 1 d) (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k), B.nabVal k' (MvPowerSeries.map (β : k →+* k') h) w0 m (MvPowerSeries.map (β : k →+* k') f) (fun l i => β (u l i)) (MvPolynomial.map (β : k →+* k') Q) = β (B.nabVal k h w0 m f u Q) := by sorry
