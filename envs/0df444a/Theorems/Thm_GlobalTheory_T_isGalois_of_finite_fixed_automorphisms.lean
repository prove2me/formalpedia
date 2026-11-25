-- Prove2me | Theorems.Thm_GlobalTheory_T_isGalois_of_finite_fixed_automorphisms
-- name    : GlobalTheory.T.isGalois_of_finite_fixed_automorphisms
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:33:58.490436+00:00
-- url     : https://prove2.me/theorems/7375911b-fddc-593e-836b-2de01745625e
-- title:
--   T: is Galois of finite fixed automorphisms
-- statement:
--   The T construction uses the is Galois of finite fixed automorphisms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaloisOfFiniteGeneratingAutomorphismsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaloisOfFiniteGeneratingAutomorphismsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaloisOfFiniteGeneratingAutomorphisms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaloisOfFiniteGeneratingAutomorphismsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isGalois_of_finite_fixed_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by sorry
