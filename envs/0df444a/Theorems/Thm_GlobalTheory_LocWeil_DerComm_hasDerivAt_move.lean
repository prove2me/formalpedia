-- Prove2me | Theorems.Thm_GlobalTheory_LocWeil_DerComm_hasDerivAt_move
-- name    : GlobalTheory.LocWeil.DerComm.hasDerivAt_move
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:13:50.184772+00:00
-- url     : https://prove2.me/theorems/06da910f-919b-4d8e-a1d8-530c66532037
-- title:
--   Der Comm: has Deriv At move
-- statement:
--   The Der Comm construction uses the has Deriv At move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L131-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtOneParameter.lean#L131-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.LocWeil GlobalTheory.LocWeil.DerComm
variable {S U : Type} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

theorem GlobalTheory.LocWeil.DerComm.hasDerivAt_move (ℓ : S →ₗ[ℂ] ℂ) (d : U →ₗ[ℝ] Module.End ℂ S) (P : ℝ → Module.End ℂ S) (hP : P 0 = 1)
    (A : Module.End ℂ S) (Φ : S) (hA : ∀ u, HasDerivAt (fun t => ℓ (P t (d u Φ))) (ℓ (A (d u Φ))) 0)
    {c : ℝ → U} {c' : U} (hc : HasDerivAt c c' 0) :
    HasDerivAt (fun t => ℓ (P t (d (c t) Φ))) (ℓ (d c' Φ + A (d (c 0) Φ))) 0 := by sorry
