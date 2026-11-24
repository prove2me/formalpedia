-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_eq_id_of_sval
-- name    : GlobalTheory.TorsionFixedAut.eq_id_of_sval
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:04.484855+00:00
-- url     : https://prove2.me/theorems/4081af94-cdb2-41cf-a7a0-926d1b80c02c
-- title:
--   Torsion Fixed Aut: eq id of sval
-- statement:
--   The Torsion Fixed Aut construction uses the eq id of sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L132-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L132-L185

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
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem GlobalTheory.TorsionFixedAut.eq_id_of_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} {ι' : Type} (s : ι' → LB.Sec (LB.LinComb L φ ε))
    (b : Y ⟶ B) (f : Y ⟶ Y) (hf : f ≫ b = b) (hcov : ⨆ i, nonzeroLocus (s i) = ⊤)
    (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ ∃ r : ι' → Γ(Y, nonzeroLocus (s i)),
      (∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ (LB.LinComb L φ ε).U k)).op).hom ((s j).f k) =
        (Y.presheaf.map (homOfLE (inf_le_left :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ nonzeroLocus (s i))).op).hom (r j) *
        (Y.presheaf.map (homOfLE (inf_le_right :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ (LB.LinComb L φ ε).U k)).op).hom ((s i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (b.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r))
    (h : ∀ y : Y, ∃ J, Good L y J ∧ ∃ u, ∀ i, sval (s i) f y J = u * sval (s i) (𝟙 Y) y J) : f = 𝟙 Y := by sorry
