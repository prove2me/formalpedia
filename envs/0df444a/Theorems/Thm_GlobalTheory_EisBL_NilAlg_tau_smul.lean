-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_tau_smul
-- name    : GlobalTheory.EisBL.NilAlg.tau_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:05.754715+00:00
-- url     : https://prove2.me/theorems/9f141e81-5a8e-495e-8259-c1aac0eab351
-- title:
--   Nil Alg: tau smul
-- statement:
--   The Nil Alg construction uses the tau smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L74-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem GlobalTheory.EisBL.NilAlg.tau_smul (c : B →+* B) (J K : Matrix n n B) (h : B) (hh : c h = h) (X : Matrix n n B) :
    tau c J K (h • X) = h • tau c J K X := by sorry
