-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_diag
-- name    : GlobalTheory.WeilDeligne.WD.lpChar_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:59:23.268902+00:00
-- url     : https://prove2.me/theorems/6f22edaa-4156-48d6-a57c-7152bd4f5d35
-- title:
--   WD: lp Char diag
-- statement:
--   The WD construction uses the lp Char diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L172-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L172-L182

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

theorem GlobalTheory.WeilDeligne.WD.lpChar_diag {ι κ : Type*} [Finite ι] [Finite κ] (c : ι → ℂˣ) (d : κ → ℂˣ) :
    lpChar (mk (WDRep.diag h c)) (mk (WDRep.diag h d)) =
      mk (WDRep.diag h fun p : ι × κ => c p.1 * d p.2) := by sorry
