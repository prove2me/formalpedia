-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_exists_apply_eq_zero_inner_eq
-- name    : GroundTheory.Automorphic.PeterssonComplement.exists_apply_eq_zero_inner_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:56.488947+00:00
-- url     : https://prove2.me/theorems/b978f568-6008-4e90-851c-257b653bf446
-- title:
--   Petersson Complement: exists apply eq zero inner eq
-- statement:
--   The Petersson Complement construction uses the exists apply eq zero inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L91-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L91-L116

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

theorem GroundTheory.Automorphic.PeterssonComplement.exists_apply_eq_zero_inner_eq (hι : Function.Injective ι) {T : Module.End ℂ V}
    (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X])
    (Z : Submodule ℂ V) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) {x : V} (hx : x ∈ Z) :
    ∃ m ∈ Z, aeval T (p.map (algebraMap ℝ ℂ)) m = 0 ∧
      ∀ w, aeval T (p.map (algebraMap ℝ ℂ)) w = 0 →
        inner ℂ (ι x) (ι w) = inner ℂ (ι m) (ι w) := by sorry
