-- Prove2me | Theorems.Thm_GlobalTheory_FlagTransport_mem_dom_coordIso
-- name    : GlobalTheory.FlagTransport.mem_dom_coordIso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:32:22.430616+00:00
-- url     : https://prove2.me/theorems/630be6c2-54d0-4b31-bae7-a09de77dd1ed
-- title:
--   Flag Transport: mem dom coord Iso
-- statement:
--   The Flag Transport construction uses the mem dom coord Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L101-L109

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
variable {X X'}

theorem GlobalTheory.FlagTransport.mem_dom_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) :
    cpt X' (baseFr X') (coordIso X X' e z) ∈ X'.dom ↔ cpt X (baseFr X) z ∈ X.dom := by sorry
