-- Prove2me | Theorems.Thm_GlobalTheory_LatticeLocBasis_exists_matrix_up_to_notMem
-- name    : GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:37.373844+00:00
-- url     : https://prove2.me/theorems/cc7fb396-548f-542a-a2d9-54e380f5e22f
-- title:
--   Lattice Loc Basis: exists matrix up to not Mem
-- statement:
--   The Lattice Loc Basis construction uses the exists matrix up to not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMatrixBasisLatticeUpToDenominatorNotMem.lean#L64-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMatrixBasisLatticeUpToDenominatorNotMem.lean#L64-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMatrixBasisLatticeUpToDenominatorNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors
open GlobalTheory GlobalTheory.LatticeLocBasis

theorem GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by sorry
