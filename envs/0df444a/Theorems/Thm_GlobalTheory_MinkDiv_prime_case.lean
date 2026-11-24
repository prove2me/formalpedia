-- Prove2me | Theorems.Thm_GlobalTheory_MinkDiv_prime_case
-- name    : GlobalTheory.MinkDiv.prime_case
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:25:47.045331+00:00
-- url     : https://prove2.me/theorems/6c3f3529-1601-4303-97fb-5b0999ad7aaf
-- title:
--   Mink Div: prime case
-- statement:
--   The Mink Div construction uses the prime case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MinkowskiDivisible.lean#L26-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MinkowskiDivisible.lean#L26-L80

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

theorem GlobalTheory.MinkDiv.prime_case (l p : ℕ) (hl : l.Prime) (ho : Odd l) (hp : p.Prime) (f : A →+ A)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x)
    (hord : ∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[p] x = x)
    (hfix : ∀ x : A, l • x = 0 → f x = x) :
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by sorry
