-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_subsingleton_of_isUnit
-- name    : GlobalTheory.DenseFibreIso.subsingleton_of_isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:43.691803+00:00
-- url     : https://prove2.me/theorems/7db2606c-567b-4b16-a251-76d7d70d407e
-- title:
--   Dense Fibre Iso: subsingleton of is Unit
-- statement:
--   The Dense Fibre Iso construction uses the subsingleton of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L37-L47

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

theorem GlobalTheory.DenseFibreIso.subsingleton_of_isUnit {N : Type} [AddCommGroup N] [Module A N] {a : A}
    (h : ∀ n : N, a • n = 0) (S : Type) [CommRing S] [Algebra A S]
    (hu : IsUnit (algebraMap A S a)) : Subsingleton (S ⊗[A] N) := by sorry
