-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_iff_ine
-- name    : GlobalTheory.WeilDeligne.WD.unr_iff_ine
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T17:01:54.159814+00:00
-- url     : https://prove2.me/theorems/c8ccdb1f-448b-4c96-a775-60bea52e062a
-- title:
--   WD: unr iff ine
-- statement:
--   The WD construction uses the unr iff ine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L227-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L227-L242

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

theorem GlobalTheory.WeilDeligne.WD.unr_iff_ine (a : WD h) :
    unr a ↔ mono0 a ∧ ∀ σ ∈ Ine (F := E) A, inePol a σ = (X - 1) ^ lpDim a := by sorry
