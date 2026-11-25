-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldBasis_existsUnique_coeff_affine
-- name    : GlobalTheory.InvFieldBasis.existsUnique_coeff_affine
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:45:17.106895+00:00
-- url     : https://prove2.me/theorems/57068aee-f7f4-4d17-a2af-a50f4ae20cc8
-- title:
--   Inv Field Basis: exists Unique coeff affine
-- statement:
--   The Inv Field Basis construction uses the exists Unique coeff affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsBasisVerticalDerivations.lean#L177-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsBasisVerticalDerivations.lean#L177-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C] {B : Type} [CommRing B] [Algebra K B]

theorem GlobalTheory.InvFieldBasis.existsUnique_coeff_affine [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    {R : Type} [CommRing R] (x₀ : R →+* K) {X : Scheme.{0}} (p : X ⟶ Sp R) (m : G.left ⟶ X)
    (H : IsPullback m G.hom p (spMap x₀)) {T : Scheme.{0}} (y : T ⟶ G.left) {W : X.Opens} (hW : IsAffineOpen W)
    {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W)) (δ : Γ(X, W) → Γ(T, V))
    (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = pbT y ((m.app W).hom f) V * δ f' + pbT y ((m.app W).hom f') V * δ f)
    (hbase : ∀ r, δ (constFn p W r) = 0) :
    ∃! c : Fin n → Γ(T, V), ∀ f, δ f = ∑ a, c a * pbT y (dd a _ ((m.app W).hom f)) V := by sorry
