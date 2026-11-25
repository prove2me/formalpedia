-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_locMap_eq_of_awayToLaurent_eq
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.locMap_eq_of_awayToLaurent_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:48.027228+00:00
-- url     : https://prove2.me/theorems/7f659461-507a-49b3-b363-073234deba5f
-- title:
--   Proj Space: loc Map eq of away To Laurent eq
-- statement:
--   The Proj Space construction uses the loc Map eq of away To Laurent eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L269-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L269-L286

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.locMap_eq_of_awayToLaurent_eq {p q : ℕ} {i : Fin p → Fin (n + 1)}
    {i' : Fin q → Fin (n + 1)} (h : Set.range i ⊆ Set.range i')
    {z : Localization.Away (xprod (A := A) i)} {z' : Localization.Away (xprod (A := A) i')}
    (hzz : awayToLaurent i z = awayToLaurent i' z') (x : ProjectiveSpectrum (grading A n))
    (hx : xprod i ∉ x.asHomogeneousIdeal) (hx' : xprod i' ∉ x.asHomogeneousIdeal) :
    ProjTwist.locMap x hx z = ProjTwist.locMap x hx' z' := by sorry
