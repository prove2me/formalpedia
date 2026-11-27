-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_sup_orthIn_eq_top_of_symmetric
-- name    : GroundTheory.Automorphic.PeterssonComplement.sup_orthIn_eq_top_of_symmetric
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:40.613302+00:00
-- url     : https://prove2.me/theorems/971caea8-5b4f-4880-8916-702e47b5d137
-- title:
--   Petersson Complement: sup orth In eq top of symmetric
-- statement:
--   The Petersson Complement construction uses the sup orth In eq top of symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L123-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L123-L146

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

theorem GroundTheory.Automorphic.PeterssonComplement.sup_orthIn_eq_top_of_symmetric (U : Submodule ℂ V) (hι : Function.Injective ι)
    {T : Module.End ℂ V} (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y)))
    (hUT : ∀ u ∈ U, T u ∈ U)
    (h : ∀ v : V, ∃ V₀ : Submodule ℂ V, v ∈ V₀ ∧ (∀ z ∈ V₀, T z ∈ V₀) ∧
      (∀ x ∈ V₀, ∃ p : ℝ[X], aeval T (p.map (algebraMap ℝ ℂ)) x = 0 ∧
        FiniteDimensional ℂ (V₀ ⊓ LinearMap.ker (aeval T (p.map (algebraMap ℝ ℂ))) : Submodule ℂ V)) ∧
      ∀ u ∈ U, ∃ e ∈ U ⊓ V₀, ∀ w ∈ V₀, inner ℂ (ι u) (ι w) = inner ℂ (ι e) (ι w)) :
    U ⊔ orthIn ι U = ⊤ := by sorry
