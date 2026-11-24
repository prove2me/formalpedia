-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_coefDet_det_scaled
-- name    : GlobalTheory.PMonE.coefDet_det_scaled
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:39.21127+00:00
-- url     : https://prove2.me/theorems/3d30c029-45fa-43b5-b267-a1b58cb83ef7
-- title:
--   PMon E: coef Det det scaled
-- statement:
--   The PMon E construction uses the coef Det det scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L52-L62

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
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem GlobalTheory.PMonE.coefDet_det_scaled {h : ℕ} (a lam y : Fin h → F) :
    (Matrix.of fun r j : Fin h => (a r * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))).det =
      (∏ r, a r ^ p ^ (h - (r : ℕ))) * ((∏ j, y j ^ p ^ h) *
        (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det) := by sorry
