-- Prove2me | Theorems.Thm_GlobalTheory_unitary_inv_eq_gram_conj
-- name    : GlobalTheory.unitary_inv_eq_gram_conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:35:50.699748+00:00
-- url     : https://prove2.me/theorems/ec95be7a-ee2d-4800-b8db-a07004844575
-- title:
--   Global Theory: unitary inv eq gram conj
-- statement:
--   The Global Theory construction uses the unitary inv eq gram conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryConjEntryAndInvEntryLinear.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitaryConjEntryAndInvEntryLinear.lean#L17-L21

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BesselJUnitaryEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryConjEntryAndInvEntryLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset Matrix
open GlobalTheory

theorem GlobalTheory.unitary_inv_eq_gram_conj {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by sorry
