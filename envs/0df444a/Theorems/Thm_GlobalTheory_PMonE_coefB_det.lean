-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_coefB_det
-- name    : GlobalTheory.PMonE.coefB_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:39:17.548862+00:00
-- url     : https://prove2.me/theorems/2c4df270-ef42-4eb6-8fbc-900993f4c9ce
-- title:
--   PMon E: coef B det
-- statement:
--   The PMon E construction uses the coef B det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L98-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L98-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE
open Finset

theorem GlobalTheory.PMonE.coefB_det (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (h : ℕ) (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hl : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hA : Antitone (fun j => ‖lam j‖)) (hO : Orth p lam) (L U : ℕ) :
    ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by sorry
