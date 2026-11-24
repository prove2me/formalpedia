-- Prove2me | Theorems.Thm_GlobalTheory_jet_sqZero_eq_lieExp
-- name    : GlobalTheory.jet_sqZero_eq_lieExp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:12.38185+00:00
-- url     : https://prove2.me/theorems/bd5978a7-25be-4671-afca-3c7b587383d3
-- title:
--   Global Theory: jet sq Zero eq lie Exp
-- statement:
--   The Global Theory construction uses the jet sq Zero eq lie Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetPointAddSqZeroEqProdMulTangent.lean#L56-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetPointAddSqZeroEqProdMulTangent.lean#L56-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstJetEqProdTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SqZero

theorem GlobalTheory.jet_sqZero_eq_lieExp {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ} {v : Fin d → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hxt : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx0 : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx1 : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    {A : Type} [CommRing A] [Algebra R A] {J : Ideal A} (hJ : J ^ 2 = ⊥) (δ : Fin d → A)
    (hδ : ∀ j, δ j ∈ J) (hδ' : ∀ j, δ j * δ j = 0) (m : ℕ) (φ : JetR R (Fin d) m →ₐ[R] A)
    (hφ : ∀ j, φ (zR m j) = δ j) : spMap φ ≫ x m = lieExp v δ hδ' := by sorry
