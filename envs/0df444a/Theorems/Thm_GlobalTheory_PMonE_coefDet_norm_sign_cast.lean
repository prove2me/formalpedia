-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_coefDet_norm_sign_cast
-- name    : GlobalTheory.PMonE.coefDet_norm_sign_cast
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:22.709612+00:00
-- url     : https://prove2.me/theorems/dfdf864e-5a21-48ff-b12e-59c38e4ca444
-- title:
--   PMon E: coef Det norm sign cast
-- statement:
--   The PMon E construction uses the coef Det norm sign cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean#L85-L87

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

theorem GlobalTheory.PMonE.coefDet_norm_sign_cast {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by sorry
