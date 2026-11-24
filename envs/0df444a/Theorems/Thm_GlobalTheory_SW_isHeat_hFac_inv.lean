-- Prove2me | Theorems.Thm_GlobalTheory_SW_isHeat_hFac_inv
-- name    : GlobalTheory.SW.isHeat_hFac_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:36.683561+00:00
-- url     : https://prove2.me/theorems/a00ea978-e271-4e0a-96ea-2e6989bb1220
-- title:
--   SW: is Heat h Fac inv
-- statement:
--   The SW construction uses the is Heat h Fac inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L240-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L240-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.isHeat_hFac_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ), ∀ γ ∈ UU E N, IsHeat Ψ (fun Z (z z' : CM Ψ n N) => (hFac Ψ γ Z z z')⁻¹) := by sorry
