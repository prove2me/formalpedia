-- Prove2me | Theorems.Thm_GlobalTheory_LocRep_rep_sub
-- name    : GlobalTheory.LocRep.rep_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:09:08.617674+00:00
-- url     : https://prove2.me/theorems/9b591e81-5d99-4c13-8ffc-6d6356e3a9dd
-- title:
--   Loc Rep: rep sub
-- statement:
--   The Loc Rep construction uses the rep sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyIntegrableRep.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyIntegrableRep.lean#L38-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.LocRep
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
open MeasureTheory
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}

theorem GlobalTheory.LocRep.rep_sub (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v - w) =ᵐ[μ] fun x => ι v x - ι w x := by sorry
