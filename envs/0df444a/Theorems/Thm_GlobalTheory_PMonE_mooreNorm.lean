-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_mooreNorm
-- name    : GlobalTheory.PMonE.mooreNorm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:39:37.206613+00:00
-- url     : https://prove2.me/theorems/be50dfc2-5a62-40c1-83f7-1ff3491f0330
-- title:
--   PMon E: moore Norm
-- statement:
--   The PMon E construction uses the moore Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L113-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L113-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
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
open Finset Polynomial

theorem GlobalTheory.PMonE.mooreNorm : MooreNorm := by sorry
