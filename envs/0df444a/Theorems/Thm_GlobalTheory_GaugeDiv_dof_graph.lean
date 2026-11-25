-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDiv_dof_graph
-- name    : GlobalTheory.GaugeDiv.dof_graph
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:12.12143+00:00
-- url     : https://prove2.me/theorems/035b43d4-75c4-493a-ba64-52fd463ca7fc
-- title:
--   Gauge Div: dof graph
-- statement:
--   The Gauge Div construction uses the dof graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L60-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L60-L99

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

theorem GlobalTheory.GaugeDiv.dof_graph {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (u v : Fin d → k) (N : ℕ) (huv : ∀ i, lin u (w i) = N * v i) (G : PS k 2 d) :
    Dof F u (ev (n := 1) ![pt k d 0, w] G) =
      ev (n := 1) ![pt k d 0, w] (DD F 0 u G + N * DD F 1 v G) := by sorry
