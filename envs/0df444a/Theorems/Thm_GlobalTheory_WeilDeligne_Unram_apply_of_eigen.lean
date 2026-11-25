-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_Unram_apply_of_eigen
-- name    : GlobalTheory.WeilDeligne.Unram.apply_of_eigen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:57:56.463708+00:00
-- url     : https://prove2.me/theorems/fa6a451d-0f15-56fc-b33f-8ce8716cf47c
-- title:
--   Unram: apply of eigen
-- statement:
--   The Unram construction uses the apply of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L36-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L36-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
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
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.Unram
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem GlobalTheory.WeilDeligne.Unram.apply_of_eigen {a : WDRep h V} (ha : a.Unr) {v : V} {c : ℂˣ}
    (hv : a.ρ (frob h) v = (c : ℂ) • v) (σ : Weil h) : a.ρ σ v = (c : ℂ) ^ deg σ • v := by sorry
