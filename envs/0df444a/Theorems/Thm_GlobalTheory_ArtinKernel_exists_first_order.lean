-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_exists_first_order
-- name    : GlobalTheory.ArtinKernel.exists_first_order
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:54.616049+00:00
-- url     : https://prove2.me/theorems/11f356b8-4c1f-4f32-bce0-862ed30db508
-- title:
--   Artin Kernel: exists first order
-- statement:
--   The Artin Kernel construction uses the exists first order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfLogDeriv.lean#L73-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfLogDeriv.lean#L73-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem GlobalTheory.ArtinKernel.exists_first_order (ρ : R →ₐ[ℂ] ℂ) (hρ : ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R)
    {U : A.left.Opens} {t : Fin g → Γ(A.left, U)} (hU : IsAffineOpen U) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U)
    (huniq : ∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) →
      (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) →
      (∀ i, D (t i) = 0) → D = 0)
    (ht : HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0)
    (x : spO R ⟶ A) (hx : resPt ρ ≫ x = u.ex 0) (hx1 : x ≠ 1) :
    ∃ (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ), κ 1 = 0 ∧ w ≠ 0 ∧
      ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := by sorry
