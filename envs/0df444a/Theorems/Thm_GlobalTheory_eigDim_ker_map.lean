-- Prove2me | Theorems.Thm_GlobalTheory_eigDim_ker_map
-- name    : GlobalTheory.eigDim_ker_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:18.07893+00:00
-- url     : https://prove2.me/theorems/2caaaae4-4d11-4456-a05e-07ecd23dc46c
-- title:
--   Global Theory: eig Dim ker map
-- statement:
--   The Global Theory construction uses the eig Dim ker map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L48-L55

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

theorem GlobalTheory.eigDim_ker_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (M.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' M)) := by sorry
