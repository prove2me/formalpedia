-- Prove2me | Theorems.Thm_GlobalTheory_CommutatorPairing_gm_unitRes
-- name    : GlobalTheory.CommutatorPairing.gm_unitRes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:42.988807+00:00
-- url     : https://prove2.me/theorems/ee6428a1-3cc4-4f52-8f8a-f6246e240821
-- title:
--   Commutator Pairing: gm unit Res
-- statement:
--   The Commutator Pairing construction uses the gm unit Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L208-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L208-L209

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

theorem GlobalTheory.CommutatorPairing.gm_unitRes {T : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) {Z : Scheme.{0}} (r : Z ⟶ V.toScheme) (z : Z) :
    gm r z ⊤ (unitRes V c) = gm (r ≫ V.ι) z ⊤ c := by sorry
