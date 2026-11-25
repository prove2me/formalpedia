-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_monomial_char_iff
-- name    : GlobalTheory.WeilDeligne.WD.monomial_char_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:01:55.573603+00:00
-- url     : https://prove2.me/theorems/008f3d43-7af5-40eb-af89-99e8fb1409e8
-- title:
--   WD: monomial char iff
-- statement:
--   The WD construction uses the monomial char iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L94-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L94-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
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
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.WD
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}

theorem GlobalTheory.WeilDeligne.WD.monomial_char_iff (a χ : WD h) (hχ : lpDim χ = 1) : mono0 (lpChar a χ) ↔ mono0 a := by sorry
