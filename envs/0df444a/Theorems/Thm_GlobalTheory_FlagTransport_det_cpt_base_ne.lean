-- Prove2me | Theorems.Thm_GlobalTheory_FlagTransport_det_cpt_base_ne
-- name    : GlobalTheory.FlagTransport.det_cpt_base_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:31:29.667086+00:00
-- url     : https://prove2.me/theorems/42a1cfb0-f733-42f8-ab3b-2c6f5ba92fbc
-- title:
--   Flag Transport: det cpt base ne
-- statement:
--   The Flag Transport construction uses the det cpt base ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L93-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralTransportHermitianFrameChartMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
open scoped Matrix
open GlobalTheory GlobalTheory.FlagTransport
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {E' : Type} [Field E'] [NumberField E'] [IsCMField E']
variable (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)

theorem GlobalTheory.FlagTransport.det_cpt_base_ne {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    (mat (cpt Y (baseFr Y) z) τ).det ≠ 0 ↔ (mat (nmat Y z) τ).det ≠ 0 := by sorry
