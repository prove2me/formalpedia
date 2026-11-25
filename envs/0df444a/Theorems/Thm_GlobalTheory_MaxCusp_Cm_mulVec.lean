-- Prove2me | Theorems.Thm_GlobalTheory_MaxCusp_Cm_mulVec
-- name    : GlobalTheory.MaxCusp.Cm_mulVec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:20.560334+00:00
-- url     : https://prove2.me/theorems/162ad082-bb8c-50c9-a98a-a4cfc89ba481
-- title:
--   Max Cusp: Cm mul Vec
-- statement:
--   The Max Cusp construction uses the Cm mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L148-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L148-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_mulVec

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

theorem GlobalTheory.MaxCusp.Cm_mulVec (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) (v : Fin r → ℂ)
    (i : Fin d) :
    (Cm X u b τ *ᵥ v) i =
      -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (Data.emb τ.1 (u k)) := by sorry
