-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_formEq_twist
-- name    : GlobalTheory.TorsionFixedAut.formEq_twist
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:24.173846+00:00
-- url     : https://prove2.me/theorems/a3f444e1-b8b6-489c-9301-8136041eb27d
-- title:
--   Torsion Fixed Aut: form Eq twist
-- statement:
--   The Torsion Fixed Aut construction uses the form Eq twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L64-L70

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

theorem GlobalTheory.TorsionFixedAut.formEq_twist (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y ⟶ Y')
    (hh : ∀ k, h ≫ φ' k = φ k ≫ σ) :
    FormEq (Sum.elim (fun k => h ≫ φ' k) (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2))
      (Sum.elim ε (fun p : K × Fin 2 => -ε p.1 * ![1, -1] p.2)) φ ε := by sorry
