-- Prove2me | Theorems.Thm_GlobalTheory_MaxCusp_exists_gamma
-- name    : GlobalTheory.MaxCusp.exists_gamma
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:51.024367+00:00
-- url     : https://prove2.me/theorems/fd7e1694-ede3-52af-bf9f-638f8a84326b
-- title:
--   Max Cusp: exists gamma
-- statement:
--   The Max Cusp construction uses the exists gamma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L361-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L361-L388

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_exists_gamma

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
variable (Y : DataX E r)

theorem GlobalTheory.MaxCusp.exists_gamma (u : Fin d → Fin r → E) (hiso : ∀ i k, herm Y.Gm (u i) (u k) = 0)
    (hmem : ∀ i, u i ∈ Y.Λ) (b : Y.Ψ → Fin d → Fin d → ℂ) (hb : b ∈ LZ Y.toData d Y.g) :
    ∃ γ ∈ Y.Γ, (∀ v ∈ Y.Λ, ∃ y ∈ Y.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (Y.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = zmat Y.toData u b τ := by sorry
