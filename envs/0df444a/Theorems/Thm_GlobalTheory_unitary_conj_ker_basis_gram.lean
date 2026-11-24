-- Prove2me | Theorems.Thm_GlobalTheory_unitary_conj_ker_basis_gram
-- name    : GlobalTheory.unitary_conj_ker_basis_gram
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:49.766826+00:00
-- url     : https://prove2.me/theorems/9fd31dfa-57b1-4ffe-abfe-bac7c7e4596c
-- title:
--   Global Theory: unitary conj ker basis gram
-- statement:
--   The Global Theory construction uses the unitary conj ker basis gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryConjMapsKerAevalBasisAndGram.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryConjMapsKerAevalBasisAndGram.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryConjMapsKerAevalBasisAndGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory

theorem GlobalTheory.unitary_conj_ker_basis_gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K)
    (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hspan : Submodule.span K (Set.range u) =
      LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
    Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
      LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
    (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) *
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by sorry
