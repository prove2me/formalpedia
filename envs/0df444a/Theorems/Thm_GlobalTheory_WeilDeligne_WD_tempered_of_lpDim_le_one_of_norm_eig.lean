-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_tempered_of_lpDim_le_one_of_norm_eig
-- name    : GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:30.724801+00:00
-- url     : https://prove2.me/theorems/00a5f75f-ee59-5a9e-8311-f8db19d9aa00
-- title:
--   WD: tempered of lp Dim le one of norm eig
-- statement:
--   The WD construction uses the tempered of lp Dim le one of norm eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TemperedOfLpDimLeOneOfUnitEigenvalues.lean#L33-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TemperedOfLpDimLeOneOfUnitEigenvalues.lean#L33-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TemperedOfLpDimLeOneOfUnitEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by sorry
