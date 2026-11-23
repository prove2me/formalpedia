-- Prove2me | Theorems.Thm_GlobalTheory_HomogMinPrime_eval_scale
-- name    : GlobalTheory.HomogMinPrime.eval_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:22.301795+00:00
-- url     : https://prove2.me/theorems/f2481bed-ee47-4315-8940-7fcfa4ca258d
-- title:
--   Homog Min Prime: eval scale
-- statement:
--   The Homog Min Prime construction uses the eval scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KerConeMemMinimalPrimes.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KerConeMemMinimalPrimes.lean#L16-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KerConeMemMinimalPrimes
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
open GlobalTheory
open GlobalTheory.HomogMinPrime
open MvPolynomial

theorem GlobalTheory.HomogMinPrime.eval_scale {o σ A : Type} [CommRing o] [CommRing A] (f : o →+* A) (g : σ → A) (c : A)
    {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    eval₂Hom f (fun a => g a * c) F = c ^ e * eval₂Hom f g F := by sorry
