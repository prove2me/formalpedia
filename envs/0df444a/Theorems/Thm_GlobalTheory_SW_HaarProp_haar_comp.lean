-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarProp_haar_comp
-- name    : GlobalTheory.SW.HaarProp.haar_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:15.78809+00:00
-- url     : https://prove2.me/theorems/79fa30ab-0843-4c57-a94c-2a475ee20e61
-- title:
--   Haar Prop: haar comp
-- statement:
--   The Haar Prop construction uses the haar comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L40-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L40-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarProp
open HaarLevel
variable {K K' κ ι κ' ι' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
  [Fintype κ] [Fintype ι] [Fintype κ'] [Fintype ι']

theorem GlobalTheory.SW.HaarProp.haar_comp (e : Matrix κ ι K ≃+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, IntM x → IntM (D • e x)) (h2 : ∀ x, IntM x → IntM (D' • e.symm x))
    (hd : Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) =
      Module.finrank ℚ K' * (Fintype.card κ' * Fintype.card ι')) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix κ' ι' K' → ℂ, IsSB φ → haar (fun m => φ (e m)) = c * haar φ := by sorry
