-- Prove2me | Theorems.Thm_GlobalTheory_SW_GaussDict_zetaOf_dot
-- name    : GlobalTheory.SW.GaussDict.zetaOf_dot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:40:57.039609+00:00
-- url     : https://prove2.me/theorems/25ef9fa8-a304-4059-b7bc-b756c7e6b5d8
-- title:
--   Gauss Dict: zeta Of dot
-- statement:
--   The Gauss Dict construction uses the zeta Of dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/GaussianQuadFormRationalCoordsHermitian.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/GaussianQuadFormRationalCoordsHermitian.lean#L80-L88

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.GaussDict
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem GlobalTheory.SW.GaussDict.zetaOf_dot (Ψ : Finset (E →+* ℂ)) (z z' : CM Ψ n N) (k : Fin n) (u : QI E N → ℂ) :
    zetaOf Ψ z z' k ⬝ᵥ u = ∑ τ : Ψ,
      (z τ k ⬝ᵥ (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) +
      z' τ k ⬝ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) := by sorry
