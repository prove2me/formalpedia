-- Prove2me | Theorems.Thm_GlobalTheory_Up_DivInFFPf_phi_inv
-- name    : GlobalTheory.Up.DivInFFPf.phi_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:54:31.545919+00:00
-- url     : https://prove2.me/theorems/44f8e3dd-75a3-40a8-8e9e-0224a4715035
-- title:
--   Div In FFPf: phi inv
-- statement:
--   The Div In FFPf construction uses the phi inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L112-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L112-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralFundSetInterLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOpenSaturation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.DivInFFPf
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa)

theorem GlobalTheory.Up.DivInFFPf.phi_inv (hN : NfacRmulStatement (E := E)) (hN' : NfacLactStatement (E := E)) (n : ℕ)
    {h : Frame X.Ψ r → ℂ} (hh : X.IsSec (Xa.Fp + n • Xa.L) h) :
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phi Xa Fl n h (lact γ (rmul x b)) = phi Xa Fl n h x := by sorry
