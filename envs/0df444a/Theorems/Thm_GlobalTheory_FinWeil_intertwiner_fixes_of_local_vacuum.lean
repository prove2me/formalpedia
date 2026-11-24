-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_intertwiner_fixes_of_local_vacuum
-- name    : GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:25:36.622635+00:00
-- url     : https://prove2.me/theorems/ac58ecdc-4215-4c8e-a7e7-360d2848f37c
-- title:
--   Fin Weil: intertwiner fixes of local vacuum
-- statement:
--   The Fin Weil construction uses the intertwiner fixes of local vacuum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntertwinerFixesOfLocalVacuum.lean#L9-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntertwinerFixesOfLocalVacuum.lean#L9-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntertwinerFixesOfLocalVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil

theorem GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (A : Submodule R X) (hA : SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M)
    (hT : ∀ x v, T (W x v) = W (φ x) (T v)) (hTe : ∀ e, Fixes W A e → T e = e) (P : X →ₗ[R] X)
    (hP : ∀ x y, γ (P x) y = γ x (P y)) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ x, φ (x - P x) = x - P x)
    (m : M) (hm : ∀ a ∈ A, W (P a) m = m) : T m = m := by sorry
