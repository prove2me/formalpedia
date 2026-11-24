-- Prove2me | Theorems.Thm_GlobalTheory_IsLatticeEmb_matrix_ext
-- name    : GlobalTheory.IsLatticeEmb.matrix_ext
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:52:54.079786+00:00
-- url     : https://prove2.me/theorems/79fc8858-b018-4720-8f4d-d326f3ea8b3d
-- title:
--   Is Lattice Emb: matrix ext
-- statement:
--   The Is Lattice Emb construction uses the matrix ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L103-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {r : ℕ}
variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']
open GlobalTheory.IsLatticeEmb
variable {φ : M →ₗ[𝓞 K] (Fin r → K)}

theorem GlobalTheory.IsLatticeEmb.matrix_ext {s : ℕ} (h : IsLatticeEmb φ) {A A' : Matrix (Fin s) (Fin r) K}
    (hA : ∀ x, A *ᵥ φ x = A' *ᵥ φ x) : A = A' := by sorry
