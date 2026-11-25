-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDiv_dmon_div
-- name    : GlobalTheory.GaugeDiv.dmon_div
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:46:23.846828+00:00
-- url     : https://prove2.me/theorems/6f80b7a0-9f8f-476f-a0b7-b0ec0afb8d1e
-- title:
--   Gauge Div: dmon div
-- statement:
--   The Gauge Div construction uses the dmon div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L268-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L268-L328

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
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
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}

theorem GlobalTheory.GaugeDiv.dmon_div {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (h1 : ev (n := 1) ![pt k d 0, 0] g = 0)
    (c1 : ∀ s, constantCoeff (pderiv k s g) = 0)
    (hl : DI φ (defL F g)) (hr : DI φ (defR F g)) {ι : Type} [Fintype ι] (U V : ι → Fin d → k)
    (hu : ∀ l i, U l i ∈ φ.range) (hv : ∀ l i, V l i ∈ φ.range) (N : ℕ)
    (huv : ∀ l i, lin (U l) (w i) = N * V l i)
    (hβ : ∀ l l', dotProduct (U l) ((bilinPart k g).mulVec (V l')) ∈ φ.range) (m : ι →₀ ℕ) :
    ∃ r : R, constantCoeff (DmonOf F U m (ev (n := 1) ![pt k d 0, w] g)) = φ (N * r) := by sorry
