-- Prove2me | Theorems.Thm_GlobalTheory_finrank_span_ringHom_comp_eq
-- name    : GlobalTheory.finrank_span_ringHom_comp_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:55:26.275929+00:00
-- url     : https://prove2.me/theorems/628a80c5-52c0-5448-a9c9-cf2b04297c02
-- title:
--   Global Theory: finrank span ring Hom comp eq
-- statement:
--   The Global Theory construction uses the finrank span ring Hom comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LinearIndependentRingHomCompIff.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LinearIndependentRingHomCompIff.lean#L30-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finrank_span_ringHom_comp_eq {A F F' : Type} [CommRing A] [Field F] [Field F']
    (φ : A →+* F) (ψ : A →+* F') (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    {ι μ : Type} [Finite ι] [Finite μ] (c : ι → μ → A) :
    Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) =
      Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) := by sorry
