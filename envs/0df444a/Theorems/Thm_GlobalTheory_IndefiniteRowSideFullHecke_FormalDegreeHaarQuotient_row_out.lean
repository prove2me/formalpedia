-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_row_out
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.row_out
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:00:49.740589+00:00
-- url     : https://prove2.me/theorems/0acfe8b2-03e2-44d8-b9c9-c83401be6c27
-- title:
--   Formal Degree Haar Quotient: row out
-- statement:
--   The Formal Degree Haar Quotient construction uses the row out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L140-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L140-L155

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.row_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by sorry
