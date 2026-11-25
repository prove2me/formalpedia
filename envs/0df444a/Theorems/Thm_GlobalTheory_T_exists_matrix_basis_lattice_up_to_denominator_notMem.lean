-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_matrix_basis_lattice_up_to_denominator_notMem
-- name    : GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:48.808038+00:00
-- url     : https://prove2.me/theorems/fd80fa4c-26a2-5212-a2ae-cbc53d25a997
-- title:
--   T: exists matrix basis lattice up to denominator not Mem
-- statement:
--   The T construction uses the exists matrix basis lattice up to denominator not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMatrixBasisLatticeUpToDenominatorNotMemStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMatrixBasisLatticeUpToDenominatorNotMemStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMatrixBasisLatticeUpToDenominatorNotMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMatrixBasisLatticeUpToDenominatorNotMemStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by sorry
