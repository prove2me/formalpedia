-- Prove2me | Theorems.Thm_GlobalTheory_BesselPeriodCompare_symmetricMeasure_l2Norm_eq_resolutionL2
-- name    : GlobalTheory.BesselPeriodCompare.symmetricMeasure_l2Norm_eq_resolutionL2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:19:34.196338+00:00
-- url     : https://prove2.me/theorems/1e03fe6f-4fca-515f-9a7a-84fd5fe19d30
-- title:
--   Bessel Period Compare: symmetric Measure l2 Norm eq resolution L2
-- statement:
--   The Bessel Period Compare construction uses the symmetric Measure l2 Norm eq resolution L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SymmetricMeasureL2NormEqResolutionL2.lean#L146-L148

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

theorem GlobalTheory.BesselPeriodCompare.symmetricMeasure_l2Norm_eq_resolutionL2 {Wp : Type*} [NormedAddCommGroup Wp]
    (ν : Measure (Mt k r)) (φ : Mat k r → Wp) :
    PI.BesselPeriodGGP.l2SG ν φ = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.sectionL2NormSq ν φ := by sorry
