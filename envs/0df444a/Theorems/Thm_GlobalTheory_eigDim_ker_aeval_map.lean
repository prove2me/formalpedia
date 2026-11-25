-- Prove2me | Theorems.Thm_GlobalTheory_eigDim_ker_aeval_map
-- name    : GlobalTheory.eigDim_ker_aeval_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:55.354566+00:00
-- url     : https://prove2.me/theorems/d5b05b22-b0c2-4d1a-92d4-c6a9907b80ca
-- title:
--   Global Theory: eig Dim ker aeval map
-- statement:
--   The Global Theory construction uses the eig Dim ker aeval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L74-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.eigDim_ker_aeval_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    Module.finrank L (LinearMap.ker (aeval (Matrix.toLin' (M.map φ)) (f.map φ))) =
      Module.finrank K (LinearMap.ker (aeval (Matrix.toLin' M) f)) := by sorry
