-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_coefDet_det_rev
-- name    : GlobalTheory.PMonE.coefDet_det_rev
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:42.313466+00:00
-- url     : https://prove2.me/theorems/897aaa97-c033-4160-bddf-79216fa2848f
-- title:
--   PMon E: coef Det det rev
-- statement:
--   The PMon E construction uses the coef Det det rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L64-L72

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

theorem GlobalTheory.PMonE.coefDet_det_rev {h : ℕ} (lam : Fin h → F) :
    (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin h)) : ℤ) : F) *
        (Matrix.of fun r j : Fin h => (lam j ^ p) ^ p ^ (r : ℕ)).det := by sorry
