-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_secCubePull_res
-- name    : GlobalTheory.AbLaw.secCubePull_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:36:13.927147+00:00
-- url     : https://prove2.me/theorems/f7493184-8bc6-4d2b-9260-edfcef7c49c9
-- title:
--   Ab Law: sec Cube Pull res
-- statement:
--   The Ab Law construction uses the sec Cube Pull res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L640-L645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L640-L645

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
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
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
variable {κ : Type} (f : X ⟶ Spec (CommRingCat.of R)) {L : LB X} (M : LB X) (D : κ → X.Opens)
variable {M}
variable {f} {f' : X' ⟶ Spec (CommRingCat.of R')} {π : X' ⟶ X} {g : R →+* R'}
  (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))

theorem GlobalTheory.AbLaw.secCubePull_res {s t : Finset κ} (h : s ⊆ t) (x : (secCube f M D).obj s) :
    secCubePull M D w t (GlobalTheory.Cube.res (secCube f M D) h x) =
      GlobalTheory.Cube.res (secCube f' (M.pull π) fun i => π ⁻¹ᵁ D i) h (secCubePull M D w s x) := by sorry
