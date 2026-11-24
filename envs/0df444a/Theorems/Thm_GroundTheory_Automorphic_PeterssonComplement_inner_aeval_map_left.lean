-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_inner_aeval_map_left
-- name    : GroundTheory.Automorphic.PeterssonComplement.inner_aeval_map_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:03.005618+00:00
-- url     : https://prove2.me/theorems/4d6a6f5c-b5f2-44e4-b80f-57e1072e7845
-- title:
--   Petersson Complement: inner aeval map left
-- statement:
--   The Petersson Complement construction uses the inner aeval map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L50-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L50-L73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}

theorem GroundTheory.Automorphic.PeterssonComplement.inner_aeval_map_left {T : Module.End ℂ V}
    (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X]) (x y : V) :
    inner ℂ (ι (aeval T (p.map (algebraMap ℝ ℂ)) x)) (ι y) =
      inner ℂ (ι x) (ι (aeval T (p.map (algebraMap ℝ ℂ)) y)) := by sorry
