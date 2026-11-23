-- Prove2me | Theorems.Thm_GlobalTheory_CommutatorPairing_prod_theta
-- name    : GlobalTheory.CommutatorPairing.prod_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:08.20306+00:00
-- url     : https://prove2.me/theorems/12448e30-34b9-4e55-ac3e-71ec8ea8a4b4
-- title:
--   Commutator Pairing: prod theta
-- statement:
--   The Commutator Pairing construction uses the prod theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L102-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}

theorem GlobalTheory.CommutatorPairing.prod_theta {T Z : Over S} (x : T ⟶ A) (t : Z ⟶ T) (a : Z ⟶ A) {U : Type} [CommGroup U]
    (h : (Z.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t a).left ≫ ![(snd T A).left, (translPt A x).left] i) ^ ![k, -k] i =
      h a.left ^ k * h ((t ≫ x) * a).left ^ (-k) := by sorry
