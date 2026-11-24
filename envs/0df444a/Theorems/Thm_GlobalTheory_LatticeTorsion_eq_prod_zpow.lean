-- Prove2me | Theorems.Thm_GlobalTheory_LatticeTorsion_eq_prod_zpow
-- name    : GlobalTheory.LatticeTorsion.eq_prod_zpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:02:08.124901+00:00
-- url     : https://prove2.me/theorems/ff0bf6fc-bdbd-4f50-95b7-779d1a4d5681
-- title:
--   Lattice Torsion: eq prod zpow
-- statement:
--   The Lattice Torsion construction uses the eq prod zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteEtaleLatticeTorsionHom.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteEtaleLatticeTorsionHom.lean#L36-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
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
open GlobalTheory GlobalTheory.LatticeTorsion
variable {S : Scheme.{0}}

theorem GlobalTheory.LatticeTorsion.eq_prod_zpow {La I A : Type} [AddCommGroup La] [Fintype I] [CommGroup A]
    (b : Module.Basis I ℤ La) (f : La → A) (hf : ∀ a c, f (a + c) = f a * f c) (a : La) :
    f a = ∏ i, f (b i) ^ (b.repr a i) := by sorry
