-- Prove2me | Theorems.Thm_GlobalTheory_ZM_SymmCommutant_core
-- name    : GlobalTheory.ZM.SymmCommutant.core
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:07.938277+00:00
-- url     : https://prove2.me/theorems/c71dbe7c-704c-4f4c-a5ba-e0608dff02e8
-- title:
--   Symm Commutant: core
-- statement:
--   The Symm Commutant construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankSymmCommutantKroneckerLe.lean#L28-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankSymmCommutantKroneckerLe.lean#L28-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankSymmCommutantKroneckerLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SymmCommutant
open Matrix

theorem GlobalTheory.ZM.SymmCommutant.core {K : Type} [Field K] {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) K)
    (hA : A.IsSymm) (hBA : B * A = 1)
    (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K) (hΘ : Θ.IsSymm)
    (H : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Θ =
      Θ * (Matrix.kronecker (B * (Matrix.single (0 : Fin 8) v (1 : K)).transpose * A)
        (1 : Matrix (Fin h) (Fin h) K)).transpose) :
    (∀ a b i j, Θ (a, i) (b, j) =
      B a b * (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j)) ∧
    ∀ i j, (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j) =
      (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, j) (0, i) := by sorry
