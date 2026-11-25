-- Prove2me | Theorems.Thm_GlobalTheory_comap_single_span_algebraMap
-- name    : GlobalTheory.comap_single_span_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:38.294467+00:00
-- url     : https://prove2.me/theorems/1b4d2894-e027-4da5-8a20-848a0b27afb3
-- title:
--   Global Theory: comap single span algebra Map
-- statement:
--   The Global Theory construction uses the comap single span algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ComapSingleSpanAlgebraMapNumberField.lean#L70-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ComapSingleSpanAlgebraMapNumberField.lean#L70-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberField
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
open GlobalTheory

theorem GlobalTheory.comap_single_span_algebraMap (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι) :
    (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap
      (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) =
    Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap
      (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by sorry
