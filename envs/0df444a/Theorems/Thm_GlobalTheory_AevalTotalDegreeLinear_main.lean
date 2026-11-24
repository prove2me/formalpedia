-- Prove2me | Theorems.Thm_GlobalTheory_AevalTotalDegreeLinear_main
-- name    : GlobalTheory.AevalTotalDegreeLinear.main
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:54:52.06083+00:00
-- url     : https://prove2.me/theorems/9b79c5ff-e25e-453e-8568-6b37b6e65a01
-- title:
--   Aeval Total Degree Linear: main
-- statement:
--   The Aeval Total Degree Linear construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeAevalLeOfLinear.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeAevalLeOfLinear.lean#L29-L30

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

theorem GlobalTheory.AevalTotalDegreeLinear.main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P := by sorry
