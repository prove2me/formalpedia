-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_summable_bound
-- name    : GlobalTheory.RealZeros.summable_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:52.666595+00:00
-- url     : https://prove2.me/theorems/e6319e5b-4d17-4e53-94ff-6492a0341071
-- title:
--   Real Zeros: summable bound
-- statement:
--   The Real Zeros construction uses the summable bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L55-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros

theorem GlobalTheory.RealZeros.summable_bound {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    Summable fun k : ℕ => C * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) := by sorry
