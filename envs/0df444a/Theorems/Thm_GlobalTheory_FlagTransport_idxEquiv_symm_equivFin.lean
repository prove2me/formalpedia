-- Prove2me | Theorems.Thm_GlobalTheory_FlagTransport_idxEquiv_symm_equivFin
-- name    : GlobalTheory.FlagTransport.idxEquiv_symm_equivFin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:31:48.724503+00:00
-- url     : https://prove2.me/theorems/078b51f9-27d7-4a55-9b1e-75ecfa76b13c
-- title:
--   Flag Transport: idx Equiv symm equiv Fin
-- statement:
--   The Flag Transport construction uses the idx Equiv symm equiv Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralTransportHermitianFrameChartMeasure.lean#L35-L40

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

theorem GlobalTheory.FlagTransport.idxEquiv_symm_equivFin (τ' : X'.Ψ) (p : {p : Fin r × Fin r // p.2 < p.1}) :
    (idxEquiv X X' e).symm (Fintype.equivFin (Ent X') (τ', p)) = Fintype.equivFin (Ent X) (e.symm τ', p) := by sorry
