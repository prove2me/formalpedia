-- Prove2me | Theorems.Thm_GlobalTheory_gs_of_eq_sum_scal
-- name    : GlobalTheory.gs_of_eq_sum_scal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:19.189776+00:00
-- url     : https://prove2.me/theorems/451ad8a8-5ada-4c9e-994f-00b0f8085052
-- title:
--   Global Theory: gs of eq sum scal
-- statement:
--   The Global Theory construction uses the gs of eq sum scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsAtIffStalks.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsAtIffStalks.lean#L26-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.gs_of_eq_sum_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) {n : ℕ} (c : Fin n → R) {a : Γ(Y, V)} {b : Fin n → Γ(Y, V)}
    (h : a = ∑ i, resTop V (scal p (c i)) * b i) :
    gs q z V a = ∑ i, cst (q ≫ p) z (c i) * gs q z V (b i) := by sorry
