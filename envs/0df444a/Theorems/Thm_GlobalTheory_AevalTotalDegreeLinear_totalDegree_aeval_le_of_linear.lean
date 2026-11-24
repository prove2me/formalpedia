-- Prove2me | Theorems.Thm_GlobalTheory_AevalTotalDegreeLinear_totalDegree_aeval_le_of_linear
-- name    : GlobalTheory.AevalTotalDegreeLinear.totalDegree_aeval_le_of_linear
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:54:59.085903+00:00
-- url     : https://prove2.me/theorems/5c55374a-cc23-469e-960b-15b7eb977509
-- title:
--   Aeval Total Degree Linear: total Degree aeval le of linear
-- statement:
--   The Aeval Total Degree Linear construction uses the total Degree aeval le of linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeAevalLeOfLinear.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeAevalLeOfLinear.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeAevalLeOfLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AevalTotalDegreeLinear
open MvPolynomial

theorem GlobalTheory.AevalTotalDegreeLinear.totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by sorry
