-- Prove2me | Theorems.Thm_GlobalTheory_ExpansionTotal_secLin_of_secScal
-- name    : GlobalTheory.ExpansionTotal.secLin_of_secScal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:03:20.176256+00:00
-- url     : https://prove2.me/theorems/980d3e67-8306-4181-a093-3ba7e097dac6
-- title:
--   Expansion Total: sec Lin of sec Scal
-- statement:
--   The Expansion Total construction uses the sec Lin of sec Scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecLinOfSecScal.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecLinOfSecScal.lean#L84-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)
omit [Algebra (FractionRing R) F]

theorem GlobalTheory.ExpansionTotal.secLin_of_secScal {X Y Y' W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₀ K K₁ : Type} [Fintype K₀] [Fintype K]
    [Fintype K₁] {φ₀ : K₀ → (W ⟶ X)} {ε₀ : K₀ → ℤ} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ₁ : K₁ → (Y' ⟶ X)}
    {ε₁ : K₁ → ℤ} {h : Y ⟶ W} (p : Y' ⟶ Y) {h' : Y' ⟶ W} (hh : h' = p ≫ h) {ρ : Y ⟶ Spec (CommRingCat.of R)}
    {π : Y' ⟶ Spec (CommRingCat.of F)} (g : R →+* F) (hπ : p ≫ ρ = π ≫ Spec.map (CommRingCat.ofHom g)) {n : ℕ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {v : Fin n → LB.Sec (LB.LinComb L φ ε)}
    {σ : Fin n → LB.Sec (LB.LinComb L φ₀ ε₀)} {c d : Fin n → F} {r : Fin n → R} (hd : ∀ i, d i * g (r i) = c i)
    (hσ : ∀ i, GeneratorPullback.SecScal L φ ε (v i) φ₀ ε₀ (σ i) h (scal ρ (r i)))
    (hs : ∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = ∑ i, constVal (𝟙 Y' ≫ π) y (c i) * sval (v i) (𝟙 Y' ≫ p) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₀ ε₀ σ h' (fun i => scal π (d i)) := by sorry
