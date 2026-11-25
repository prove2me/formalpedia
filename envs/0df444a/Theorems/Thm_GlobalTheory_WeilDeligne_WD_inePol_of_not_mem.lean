-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_inePol_of_not_mem
-- name    : GlobalTheory.WeilDeligne.WD.inePol_of_not_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:57:28.44807+00:00
-- url     : https://prove2.me/theorems/379b2b27-9978-584d-a82d-c4e48b5b0de8
-- title:
--   WD: ine Pol of not mem
-- statement:
--   The WD construction uses the ine Pol of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L546-L546
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L546-L546

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
open GlobalTheory.WeilDeligne.WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem GlobalTheory.WeilDeligne.WD.inePol_of_not_mem (x : WD h) {σ : G E Ω} (hσ : σ ∉ Weil h) : inePol x σ = 1 := by sorry
