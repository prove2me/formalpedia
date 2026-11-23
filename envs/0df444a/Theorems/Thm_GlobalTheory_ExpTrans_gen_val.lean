-- Prove2me | Theorems.Thm_GlobalTheory_ExpTrans_gen_val
-- name    : GlobalTheory.ExpTrans.gen_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:31.519104+00:00
-- url     : https://prove2.me/theorems/1eb6f376-66ca-47ea-ad83-4aed4e77e747
-- title:
--   Exp Trans: gen val
-- statement:
--   The Exp Trans construction uses the gen val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsAtTransport.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsAtTransport.lean#L39-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {X X' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
variable (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)

theorem GlobalTheory.ExpTrans.gen_val (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L' φ' ε))
    (H : PMaps w φ' φ ε t' t h) (z : Y') {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t h z J = (∏ κ, om w z J J' (φ' κ) ^ ε κ) * val t' (𝟙 _) z J' := by sorry
