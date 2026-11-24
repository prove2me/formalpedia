-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_norm_br_le
-- name    : GlobalTheory.RealZeros.norm_br_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:46.443143+00:00
-- url     : https://prove2.me/theorems/f675662e-fadc-4e5e-a361-183b9b97bddc
-- title:
--   Real Zeros: norm br le
-- statement:
--   The Real Zeros construction uses the norm br le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L30-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L30-L53

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

theorem GlobalTheory.RealZeros.norm_br_le {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) (k : ℕ) {s : ℂ} {ε R : ℝ}
    (hε : 0 < ε) (hs : ε < s.re) (hR : ‖s‖ < R) :
    ‖br N c d k s‖ ≤ R * d * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) := by sorry
