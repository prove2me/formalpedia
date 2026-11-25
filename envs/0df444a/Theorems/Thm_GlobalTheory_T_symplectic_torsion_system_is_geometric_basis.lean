-- Prove2me | Theorems.Thm_GlobalTheory_T_symplectic_torsion_system_is_geometric_basis
-- name    : GlobalTheory.T.symplectic_torsion_system_is_geometric_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:24.226943+00:00
-- url     : https://prove2.me/theorems/abc690db-12c9-5603-a076-85f67708fb95
-- title:
--   T: symplectic torsion system is geometric basis
-- statement:
--   The T construction uses the symplectic torsion system is geometric basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymplecticTorsionSystemIsGeometricBasisStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymplecticTorsionSystemIsGeometricBasisStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasisStatement
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

theorem GlobalTheory.T.symplectic_torsion_system_is_geometric_basis : Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by sorry
