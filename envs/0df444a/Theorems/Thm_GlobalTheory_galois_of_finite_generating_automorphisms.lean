-- Prove2me | Theorems.Thm_GlobalTheory_galois_of_finite_generating_automorphisms
-- name    : GlobalTheory.galois_of_finite_generating_automorphisms
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:30.707817+00:00
-- url     : https://prove2.me/theorems/1cbe4a34-bb0e-4f3a-ae2b-a7950dd42e2b
-- title:
--   Global Theory: galois of finite generating automorphisms
-- statement:
--   The Global Theory construction uses the galois of finite generating automorphisms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaloisOfFiniteGeneratingAutomorphisms.lean#L5-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaloisOfFiniteGeneratingAutomorphisms.lean#L5-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaloisOfFiniteGeneratingAutomorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.galois_of_finite_generating_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by sorry
