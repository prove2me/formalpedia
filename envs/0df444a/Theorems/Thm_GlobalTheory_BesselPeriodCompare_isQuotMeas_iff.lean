-- Prove2me | Theorems.Thm_GlobalTheory_BesselPeriodCompare_isQuotMeas_iff
-- name    : GlobalTheory.BesselPeriodCompare.isQuotMeas_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:20:08.031797+00:00
-- url     : https://prove2.me/theorems/919e6f36-3184-4115-b61f-1e9ba9a3f3d9
-- title:
--   Bessel Period Compare: is Quot Meas iff
-- statement:
--   The Bessel Period Compare construction uses the is Quot Meas iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L109-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L109-L137

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

theorem GlobalTheory.BesselPeriodCompare.isQuotMeas_iff {G S : Set (Mat k r)} (hG : IsClosedSubgroup G) (hSG : S ⊆ G)
    {μG μS : Measure (Mt k r)} (h1 : μG {x | Matrix.of x ∉ G} = 0)
    (h2 : μS {x | Matrix.of x ∉ S} = 0) (h3 : μS ≠ 0) (ν : Measure (Mt k r)) :
    PI.BesselPeriodGGP.IsQuotMeas μG μS ν ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsQuotRep G μG μS ν := by sorry
