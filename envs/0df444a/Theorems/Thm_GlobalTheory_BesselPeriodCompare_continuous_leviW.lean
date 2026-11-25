-- Prove2me | Theorems.Thm_GlobalTheory_BesselPeriodCompare_continuous_leviW
-- name    : GlobalTheory.BesselPeriodCompare.continuous_leviW
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:23.269997+00:00
-- url     : https://prove2.me/theorems/546fcb71-ff7a-54c5-a760-421ec69de813
-- title:
--   Bessel Period Compare: continuous levi W
-- statement:
--   The Bessel Period Compare construction uses the continuous levi W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L201-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L201-L207

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

theorem GlobalTheory.BesselPeriodCompare.continuous_leviW : Continuous (leviW k r) := by sorry
