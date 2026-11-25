-- Prove2me | Theorems.Thm_GlobalTheory_TorusRoot_exists_root_fin
-- name    : GlobalTheory.TorusRoot.exists_root_fin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:12:55.407814+00:00
-- url     : https://prove2.me/theorems/a8d8e84a-7b89-494c-8884-6d946b55d8bb
-- title:
--   Torus Root: exists root fin
-- statement:
--   The Torus Root construction uses the exists root fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsPthRootTorusPointNilpotentAugmentedExt.lean#L86-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsPthRootTorusPointNilpotentAugmentedExt.lean#L86-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPthRootTorusPointNilpotentAugmentedExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TorusRoot

theorem GlobalTheory.TorusRoot.exists_root_fin (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (_ : IsNilpotent (RingHom.ker π))
    (a : Fin n → Aˣ) (_ : ∀ i, π (a i).val = 1),
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : Fin n → A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      (∀ i, π' (s i).val = 1) ∧ ∀ i, s i ^ p = Units.map (f : A →* A') (a i) := by sorry
