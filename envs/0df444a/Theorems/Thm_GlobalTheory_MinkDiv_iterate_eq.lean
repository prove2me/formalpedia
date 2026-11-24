-- Prove2me | Theorems.Thm_GlobalTheory_MinkDiv_iterate_eq
-- name    : GlobalTheory.MinkDiv.iterate_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:25:15.667678+00:00
-- url     : https://prove2.me/theorems/1cda4886-d21e-4b7b-acc1-e321c06a9cce
-- title:
--   Mink Div: iterate eq
-- statement:
--   The Mink Div construction uses the iterate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MinkowskiDivisible.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MinkowskiDivisible.lean#L16-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinkowskiDivisible
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.MinkDiv
variable {A : Type} [AddCommGroup A]

theorem GlobalTheory.MinkDiv.iterate_eq (f g : A →+ A) (hfg : ∀ z, f z = z + g z) (y : A) (hy : g (g (g y)) = 0)
    (n : ℕ) : f^[n] y = y + n • g y + (n.choose 2) • g (g y) := by sorry
