-- Prove2me | Theorems.Thm_GlobalTheory_BesselPeriodCompare_isHCParam_of_interlaces
-- name    : GlobalTheory.BesselPeriodCompare.isHCParam_of_interlaces
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:18:52.281271+00:00
-- url     : https://prove2.me/theorems/337ffe63-27c3-4f5b-926f-acd8a1d661c8
-- title:
--   Bessel Period Compare: is HCParam of interlaces
-- statement:
--   The Bessel Period Compare construction uses the is HCParam of interlaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L363-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L363-L380

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

theorem GlobalTheory.BesselPeriodCompare.isHCParam_of_interlaces {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hi : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.Interlaces r k lam u)
    (hp : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.Parity r k lam u) : Formalism.QuantumDeterminants.IsHCParam u := by sorry
