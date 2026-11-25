-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_frobEig_tw
-- name    : GlobalTheory.WeilDeligne.WD.frobEig_tw
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:57:38.088876+00:00
-- url     : https://prove2.me/theorems/45046e7b-068d-59d6-a39b-57f6a171c210
-- title:
--   WD: frob Eig tw
-- statement:
--   The WD construction uses the frob Eig tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L164-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L164-L170

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
open GlobalTheory.WeilDeligne.WD
open Unram

theorem GlobalTheory.WeilDeligne.WD.frobEig_tw (a : WD h) (s : ℝ) (ha : unr a) :
    frobEig (lpTw a s) = (frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) := by sorry
