-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpUnr_spec
-- name    : GlobalTheory.WeilDeligne.WD.lpUnr_spec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:57:38.998074+00:00
-- url     : https://prove2.me/theorems/847be7bb-43fc-587b-8884-be756369c938
-- title:
--   WD: lp Unr spec
-- statement:
--   The WD construction uses the lp Unr spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L115-L123

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

theorem GlobalTheory.WeilDeligne.WD.lpUnr_spec (m : Multiset ℂ) (hm : (0 : ℂ) ∉ m) :
    unr (lpUnr h m) ∧ frobEig (lpUnr h m) = m ∧ lpDim (lpUnr h m) = Multiset.card m := by sorry
