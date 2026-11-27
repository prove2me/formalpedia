-- Prove2me | Theorems.Thm_GlobalTheory_T_unitary_conj_maps_ker_aeval_basis_and_gram
-- name    : GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:59.580322+00:00
-- url     : https://prove2.me/theorems/b067c0ed-8b5c-55cb-b261-a8df226277d1
-- title:
--   T: unitary conj maps ker aeval basis and gram
-- statement:
--   The T construction uses the unitary conj maps ker aeval basis and gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryConjMapsKerAevalBasisAndGramStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryConjMapsKerAevalBasisAndGramStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryConjMapsKerAevalBasisAndGram
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryConjMapsKerAevalBasisAndGramStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1 → ∀ (Q : K[X]) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q)) → LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧ Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) = LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧ (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by sorry
