-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_isUnit_det_of_mem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.isUnit_det_of_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:00:46.047672+00:00
-- url     : https://prove2.me/theorems/0e801cb1-3c45-4f74-bc70-2780ecbc4db7
-- title:
--   Formal Degree Haar Quotient: is Unit det of mem
-- statement:
--   The Formal Degree Haar Quotient construction uses the is Unit det of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L177-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L177-L182

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open PI.BesselMapUniq (psiGen)
variable {k r : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.isUnit_det_of_mem {h : Mat k r} (hh : h ∈ UH (Hpk k r)) (hH : IsUnit (Hpk k r).det) :
    IsUnit h.det := by sorry
