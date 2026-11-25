-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDatum_main
-- name    : GlobalTheory.PeriodDatum.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T17:38:22.874861+00:00
-- url     : https://prove2.me/theorems/e509d397-3cd5-54d8-934a-6aafd1f753ec
-- title:
--   Period Datum: main
-- statement:
--   The Period Datum construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsCompatibleBasis.lean#L82-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsCompatibleBasis.lean#L82-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TeichmullerQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DualTowerMapExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEndDifferentialRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLiftOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GroupLawPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FiniteAlgebraSplitLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinEtaleFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsCompatibleBasis
import Theorems.Thm_GlobalTheory_FinOf_main
import Theorems.Thm_GlobalTheory_PadicOrderAction_main
import Theorems.Thm_GlobalTheory_SmoothNilLift_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PeriodDatum

theorem GlobalTheory.PeriodDatum.main :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ)
    (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (B : BX (Ainf.R0 p O ε))
    (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, ∃ y, p • y = x) → Nat.card {x : B.G (Ainf.ainfTowerL p O hv ε hε).O // p • x = 0} = p ^ (2 * g) →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • x = 0 → (∀ y : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O),
    (∀ a, (Ad a).ab = (Ad (cj a)).a) → (∀ a, cj (cj a) = a) →
    (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R), (Ad 1).a.f s x = x ∧ ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
      (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) →
    ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c),
      D.H.P = 0 ∧ D.H.PL = 0 ∧
      (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧
      ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by sorry
