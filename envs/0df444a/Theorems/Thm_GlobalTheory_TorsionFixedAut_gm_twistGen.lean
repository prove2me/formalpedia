-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_gm_twistGen
-- name    : GlobalTheory.TorsionFixedAut.gm_twistGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:31.963898+00:00
-- url     : https://prove2.me/theorems/e304a23d-51a8-4462-a58a-aa4f41e5e612
-- title:
--   Torsion Fixed Aut: gm twist Gen
-- statement:
--   The Torsion Fixed Aut construction uses the gm twist Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L36-L42

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

theorem GlobalTheory.TorsionFixedAut.gm_twistGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : K × Fin 2 → L.ι)
    (hj : r z ∈ LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j) :
    gm r z (LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j) ((twistGen c φ ε).s j) =
      ∏ k, gm r z (LB.wchart L (fun b => φ k ≫ ![σ, 𝟙 X] b) (fun b => j (k, b)))
        ((LB.pullGen L _ _ c (φ k)).s (fun b => j (k, b))) ^ (-ε k) := by sorry
