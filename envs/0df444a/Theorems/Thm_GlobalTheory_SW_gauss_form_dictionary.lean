-- Prove2me | Theorems.Thm_GlobalTheory_SW_gauss_form_dictionary
-- name    : GlobalTheory.SW.gauss_form_dictionary
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:28.552284+00:00
-- url     : https://prove2.me/theorems/8b0c2df8-449d-43b8-85df-3adfb524197f
-- title:
--   SW: gauss form dictionary
-- statement:
--   The SW construction uses the gauss form dictionary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/GaussianQuadFormRationalCoordsHermitian.lean#L119-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/GaussianQuadFormRationalCoordsHermitian.lean#L119-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_GaussianQuadFormRationalCoordsHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.gauss_form_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by sorry
