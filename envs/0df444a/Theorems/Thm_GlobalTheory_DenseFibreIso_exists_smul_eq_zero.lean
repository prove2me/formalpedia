-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_exists_smul_eq_zero
-- name    : GlobalTheory.DenseFibreIso.exists_smul_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:38.167061+00:00
-- url     : https://prove2.me/theorems/9b442a67-f712-454e-ad08-311d7f3d704a
-- title:
--   Dense Fibre Iso: exists smul eq zero
-- statement:
--   The Dense Fibre Iso construction uses the exists smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L16-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
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
open GlobalTheory GlobalTheory.DenseFibreIso
variable {A : Type} [CommRing A]

theorem GlobalTheory.DenseFibreIso.exists_smul_eq_zero {N : Type} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (A' : Type) [CommRing A'] [Algebra A A'] [Subsingleton (A' ⊗[A] N)] (m : PrimeSpectrum A') :
    ∃ a : A, algebraMap A A' a ∉ m.asIdeal ∧ ∀ n : N, a • n = 0 := by sorry
