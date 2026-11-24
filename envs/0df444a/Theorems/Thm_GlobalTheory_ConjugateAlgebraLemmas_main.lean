-- Prove2me | Theorems.Thm_GlobalTheory_ConjugateAlgebraLemmas_main
-- name    : GlobalTheory.ConjugateAlgebraLemmas.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:26.816523+00:00
-- url     : https://prove2.me/theorems/78ea4679-dd83-4384-bfd3-c3275f6ddc0e
-- title:
--   Conjugate Algebra Lemmas: main
-- statement:
--   The Conjugate Algebra Lemmas construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L45-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjAlgApply.lean#L45-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateAlgebraLemmas
open Matrix

theorem GlobalTheory.ConjugateAlgebraLemmas.main : ∀ {K : Type} [inst : Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), Matrix.transpose (Matrix.map (↑g : Matrix (Fin n) (Fin n) K) (⇑σ : K → K)) * (↑g : Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin n) (Fin n) K) → ∀ (Q : Polynomial K) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) → (LinearIndependent K fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) ∧ Submodule.span K (Set.range fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑γ : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) ∧ ((Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i) k) * Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u j) k) = (Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (u i k) * u j k := by sorry
