-- Prove2me | Theorems.Thm_GlobalTheory_SquareDensity_eval_aeval
-- name    : GlobalTheory.SquareDensity.eval_aeval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:43.871107+00:00
-- url     : https://prove2.me/theorems/22dae7b5-66ad-4d15-8663-349084ab6246
-- title:
--   Square Density: eval aeval
-- statement:
--   The Square Density construction uses the eval aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L43-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSqAddSubDvd
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
open GlobalTheory.SquareDensity

theorem GlobalTheory.SquareDensity.eval_aeval {K σ : Type*} [CommRing K] (Φ : MvPolynomial σ K) (a : σ → Polynomial K)
    (t : K) :
    (MvPolynomial.aeval a Φ).eval t = MvPolynomial.eval (fun i => (a i).eval t) Φ := by sorry
