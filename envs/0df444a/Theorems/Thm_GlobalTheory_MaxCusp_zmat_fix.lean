-- Prove2me | Theorems.Thm_GlobalTheory_MaxCusp_zmat_fix
-- name    : GlobalTheory.MaxCusp.zmat_fix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:48.631139+00:00
-- url     : https://prove2.me/theorems/b2028af6-c726-5861-89af-c10cf519dfcc
-- title:
--   Max Cusp: zmat fix
-- statement:
--   The Max Cusp construction uses the zmat fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L166-L169

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
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

theorem GlobalTheory.MaxCusp.zmat_fix (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) (i : Fin d) :
    zmat X u b τ *ᵥ Data.emb τ.1 (u i) = Data.emb τ.1 (u i) := by sorry
