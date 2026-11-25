-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_leviW_mul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.leviW_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:59:37.767874+00:00
-- url     : https://prove2.me/theorems/595f4cb0-bbbd-555e-b1d6-03ad540e5f54
-- title:
--   Formal Degree Haar Quotient: levi W mul
-- statement:
--   The Formal Degree Haar Quotient construction uses the levi W mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L157-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L157-L175

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.leviW_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : leviW k r (h * n) = h := by sorry
