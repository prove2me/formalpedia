-- Prove2me | Theorems.Thm_GlobalTheory_SeriesNakayama_surjective_of_mod
-- name    : GlobalTheory.SeriesNakayama.surjective_of_mod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:14.498002+00:00
-- url     : https://prove2.me/theorems/109c3c0a-63a7-4e6e-b3bb-2d399bc407e6
-- title:
--   Series Nakayama: surjective of mod
-- statement:
--   The Series Nakayama construction uses the surjective of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L23-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama

theorem GlobalTheory.SeriesNakayama.surjective_of_mod {O ι κ : Type*} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (Φ : (ι → O) →ₗ[O] (κ → O))
    (h : ∀ G : κ → O, ∃ x, ∀ j, G j - Φ x j ∈ Ideal.span {π}) : Function.Surjective Φ := by sorry
