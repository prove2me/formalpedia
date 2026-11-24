-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_exists_linear_of_first_order
-- name    : GlobalTheory.ArtinKernel.exists_linear_of_first_order
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:22.727594+00:00
-- url     : https://prove2.me/theorems/25d6094d-6693-4e19-a305-1324844d4a20
-- title:
--   Artin Kernel: exists linear of first order
-- statement:
--   The Artin Kernel construction uses the exists linear of first order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TranslationFixingBundleArtinPointEqOne.lean#L40-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TranslationFixingBundleArtinPointEqOne.lean#L40-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TranslationFixingBundleArtinPointEqOne
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

theorem GlobalTheory.ArtinKernel.exists_linear_of_first_order (hL : L.IsLB) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ))
    (ha : ∀ l, a l ≠ 0)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l))
    (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (hx : resPt ρ ≫ x = 1) (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ)
    (hκ : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)
    (c : LB.Gen (Out.translDiff A L x)) (hc : c.IsGen) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : u.Λ, B l w = lam l := by sorry
