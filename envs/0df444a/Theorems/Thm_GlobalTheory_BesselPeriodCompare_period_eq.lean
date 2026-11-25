-- Prove2me | Theorems.Thm_GlobalTheory_BesselPeriodCompare_period_eq
-- name    : GlobalTheory.BesselPeriodCompare.period_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:18:59.270047+00:00
-- url     : https://prove2.me/theorems/a1b95ba9-6e55-5310-b8b3-4758989f3006
-- title:
--   Bessel Period Compare: period eq
-- statement:
--   The Bessel Period Compare construction uses the period eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L338-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L338-L361

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
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

theorem GlobalTheory.BesselPeriodCompare.period_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN μS : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn (Sset k r z) μS) :
    ∃ t : ℝ, 0 < t ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (c : Fin r → ℂ)
      (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (w v : H),
      GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period k r z c σ π μS w v =
        t • ∫ p : Mt k r × Mt k r,
          (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
            star (PI.BesselPeriodGGP.psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
          ∂(μW.prod μN) := by sorry
