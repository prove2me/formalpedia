-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_val_twistGen
-- name    : GlobalTheory.TorsionFixedAut.val_twistGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:32.431813+00:00
-- url     : https://prove2.me/theorems/3a9939b8-6f95-4abf-a6b0-334ac561bf47
-- title:
--   Torsion Fixed Aut: val twist Gen
-- statement:
--   The Torsion Fixed Aut construction uses the val twist Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L56-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
variable {σ : X ⟶ X} (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1]))

theorem GlobalTheory.TorsionFixedAut.val_twistGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (twistGen c φ ε) r z J = (∏ k, val c (r ≫ φ k) z J ^ ε k)⁻¹ := by sorry
