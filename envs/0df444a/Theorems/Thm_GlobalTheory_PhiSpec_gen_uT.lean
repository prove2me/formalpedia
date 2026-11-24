-- Prove2me | Theorems.Thm_GlobalTheory_PhiSpec_gen_uT
-- name    : GlobalTheory.PhiSpec.gen_uT
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:45:02.124927+00:00
-- url     : https://prove2.me/theorems/badd8eb2-284b-4b73-a546-29abb242f25d
-- title:
--   Phi Spec: gen u T
-- statement:
--   The Phi Spec construction uses the gen u T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L47-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L47-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
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
open GlobalTheory
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}

theorem GlobalTheory.PhiSpec.gen_uT (k : ℕ) (α α' : D.X) (m : T ⟶ D.P.A)
    (hα : cP D _ α' = cP D _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → (T.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D _ α).left * h m.left * (h (1 : T ⟶ D.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : T ⟶ D.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (fun i => (snd T D.P.A).left ≫ D.famφB α' i)
        (fun i => (trT D m ≫ snd _ _).left ≫ D.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J), Good D.P.L z J →
        val u ρ.left z J = uT D k α m ρ z J * val vO (ρ ≫ fst _ _).left z J := by sorry
