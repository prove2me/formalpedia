-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_spec
-- name    : GlobalTheory.isoTransvection_spec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:42.896315+00:00
-- url     : https://prove2.me/theorems/ec9bf15e-1785-4153-9c58-99b69059cc67
-- title:
--   Global Theory: iso Transvection spec
-- statement:
--   The Global Theory construction uses the iso Transvection spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L333-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L333-L360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module

theorem GlobalTheory.isoTransvection_spec {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M]
    [Module R M] (h : M →ₗ[R] M →ₗ⋆[R] R) (hh : ∀ u v, h v u = star (h u v))
    (x : M) (hx : h x x = 0) :
    (∀ b v, isoTransvectionHom h x hx (Multiplicative.ofAdd b) v = v + (b * h v x) • x) ∧
    (∀ b, isoTransvectionHom h x hx (Multiplicative.ofAdd b) = isoTransvection h x hx b) ∧
    (∀ b b', isoTransvection h x hx b * isoTransvection h x hx b'
      = isoTransvection h x hx (b + b')) ∧
    (∀ b, isoTransvection h x hx b x = x) ∧
    (∀ b v, h (isoTransvection h x hx b v) x = h v x) ∧
    (∀ b u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (b + star b) * h u x * h x v) ∧
    (∀ b u v, h (isoTransvection h x hx b u) v = h u (isoTransvection h x hx (star b) v)) ∧
    (Module.Free R M → Module.Finite R M →
      ∀ b, LinearMap.det (isoTransvection h x hx b : M →ₗ[R] M) = 1) ∧
    (∀ b, b + star b = 0 →
      ∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v) ∧
    (∀ (R₀ : Subring R) (L : Submodule R₀ M) (I : Ideal R₀) (b : R₀), x ∈ L →
      (∀ v ∈ L, h v x ∈ R₀) → b ∈ I →
        (∀ v ∈ L, isoTransvection h x hx b v - v ∈ I • L) ∧
          isoTransvection h x hx b '' (L : Set M) = L) := by sorry
