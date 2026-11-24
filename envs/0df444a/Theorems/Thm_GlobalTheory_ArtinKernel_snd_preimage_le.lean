-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_snd_preimage_le
-- name    : GlobalTheory.ArtinKernel.snd_preimage_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:59:04.143833+00:00
-- url     : https://prove2.me/theorems/5e3e3407-3508-45f8-a641-580b60617c9a
-- title:
--   Artin Kernel: snd preimage le
-- statement:
--   The Artin Kernel construction uses the snd preimage le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfLogDeriv.lean#L444-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfLogDeriv.lean#L444-L473

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

theorem GlobalTheory.ArtinKernel.snd_preimage_le (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (hx : resPt ρ ≫ x = 1) (i : L.ι) :
    (snd (spO R) A).left ⁻¹ᵁ L.U i ≤ (Out.translDiff A L x).U (fun _ => i) := by sorry
