-- Prove2me | Theorems.Thm_GlobalTheory_MaxCusp_Zb_dom
-- name    : GlobalTheory.MaxCusp.Zb_dom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:34:53.819516+00:00
-- url     : https://prove2.me/theorems/a1974b3c-7f76-48ef-a3c9-5acaf2a13e19
-- title:
--   Max Cusp: Zb dom
-- statement:
--   The Max Cusp construction uses the Zb dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L214-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L214-L220

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Zb_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Zb_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
variable (X : Data E r)

theorem GlobalTheory.MaxCusp.Zb_dom (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Zb X u b x ∈ X.dom := by sorry
