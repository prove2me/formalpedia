-- Prove2me | Theorems.Thm_GlobalTheory_SW_GaussDict_tauOf_mulVec
-- name    : GlobalTheory.SW.GaussDict.tauOf_mulVec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:17.960809+00:00
-- url     : https://prove2.me/theorems/3fb884c4-98bd-4865-8eb4-4d78f6d7eaa9
-- title:
--   Gauss Dict: tau Of mul Vec
-- statement:
--   The Gauss Dict construction uses the tau Of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/GaussianQuadFormRationalCoordsHermitian.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/GaussianQuadFormRationalCoordsHermitian.lean#L68-L78

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

theorem GlobalTheory.SW.GaussDict.tauOf_mulVec (Ψ : Finset (E →+* ℂ)) (Y : CM Ψ N N) (u : QI E N → ℂ) (p : QI E N) :
    (tauOf Ψ Y *ᵥ u) p = ∑ τ : Ψ, (τ.1 (Module.finBasis ℚ E p.2) *
      (Y τ *ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) p.1 +
      conj (τ.1 (Module.finBasis ℚ E p.2)) *
      ((Y τ)ᵀ *ᵥ fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) p.1) := by sorry
