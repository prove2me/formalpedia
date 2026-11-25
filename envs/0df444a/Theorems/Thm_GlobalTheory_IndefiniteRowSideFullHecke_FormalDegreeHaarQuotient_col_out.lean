-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_col_out
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.col_out
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:52:43.8465+00:00
-- url     : https://prove2.me/theorems/cac898f5-f853-43ed-a947-5be0a7cbbc89
-- title:
--   Formal Degree Haar Quotient: col out
-- statement:
--   The Formal Degree Haar Quotient construction uses the col out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L119-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean#L119-L130

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.col_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by sorry
