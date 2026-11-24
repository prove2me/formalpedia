-- Prove2me | Theorems.Thm_GlobalTheory_latContMap_repr
-- name    : GlobalTheory.latContMap_repr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:30.321989+00:00
-- url     : https://prove2.me/theorems/ff8f57b5-ea48-41c2-88dd-6c5f47e16acf
-- title:
--   Global Theory: lat Cont Map repr
-- statement:
--   The Global Theory construction uses the lat Cont Map repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LatContMapContinuous.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LatContMapContinuous.lean#L36-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LatContMapContinuous
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

theorem GlobalTheory.latContMap_repr {La E J : Type} [AddCommGroup La] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] (e : Module.Basis J ℤ La) (p : La →+ E) (n : J → ℤ) :
    latContMap (fun i => p (e i)) (fun i => (n i : ℝ)) = p (e.equivFun.symm n) := by sorry
