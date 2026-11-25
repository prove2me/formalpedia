-- Prove2me | Theorems.Thm_GlobalTheory_BesselPeriodCompare_typings_equiv
-- name    : GlobalTheory.BesselPeriodCompare.typings_equiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:27.476025+00:00
-- url     : https://prove2.me/theorems/21d2588d-4793-4978-bc8a-4684dd46d53b
-- title:
--   Bessel Period Compare: typings equiv
-- statement:
--   The Bessel Period Compare construction uses the typings equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L418-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L418-L454

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_typings_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.BesselPeriodCompare
open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open Formalism.FourierDecayAlt.B2 (IsClosedSubgroup mulM invM)
open Formalism.FourierDecayAlt.P.B2x1
open GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient (Mat leviW IsClosedMatGroup)
variable {k r : ℕ}

theorem GlobalTheory.BesselPeriodCompare.typings_equiv :
    (∀ (k r : ℕ) (U : Set (Mat k r)), IsClosedMatGroup U → ∀ μ : Measure (Mt k r),
      PI.BesselPeriodGGP.IsHaarOn U μ ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ) ∧
    (∀ (k r : ℕ) (G S : Set (Mat k r)), IsClosedMatGroup G → S ⊆ G → ∀ μG μS ν : Measure (Mt k r),
      PI.BesselPeriodGGP.IsHaarOn G μG → PI.BesselPeriodGGP.IsHaarOn S μS →
      (PI.BesselPeriodGGP.IsQuotMeas μG μS ν ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsQuotRep G μG μS ν)) ∧
    (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ),
      IsClosedMatGroup (UH (Hpk k r)) ∧ IsClosedMatGroup (UWset k r z) ∧ IsClosedMatGroup (Nset k r) ∧
        (inWb k r z → IsClosedMatGroup (Sset k r z))) ∧
    (∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
      (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (φ : Mat k r → Wp),
      PI.BesselPeriodGGP.IsSPsiEquiv z (PI.BesselPeriodGGP.psiGen k r z c) π φ ↔
        GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsEquivariant k r z c π φ) ∧
    (∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] (ν : Measure (Mt k r)) (φ : Mat k r → Wp),
      PI.BesselPeriodGGP.l2SG ν φ = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.sectionL2NormSq ν φ) ∧
    (∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure (Mt k r))
      (σ : Mat k r → (H →L[ℂ] H)) (w : H),
      AEStronglyMeasurable (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ) μ →
      PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w) ∧
    (∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (σ : Mat k r → (H →L[ℂ] H)),
      PI.UpqRep.IsDSHpk k r ε lam σ → ∀ μ : Measure (Mt k r),
      PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μ → ∀ w : H,
      PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w) ∧
    (PI.BesselPeriodGGP.BesselPeriodGGP ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.BesselPeriodNeZero) := by sorry
