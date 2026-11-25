-- Prove2me | Theorems.Thm_GlobalTheory_T_comap_single_span_algebraMap_numberField
-- name    : GlobalTheory.T.comap_single_span_algebraMap_numberField
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:52.515807+00:00
-- url     : https://prove2.me/theorems/6e578602-18a2-4a49-912d-8f76afe961c7
-- title:
--   T: comap single span algebra Map number Field
-- statement:
--   The T construction uses the comap single span algebra Map number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ComapSingleSpanAlgebraMapNumberFieldStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ComapSingleSpanAlgebraMapNumberFieldStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.comap_single_span_algebraMap_numberField : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι), (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) = Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by sorry
