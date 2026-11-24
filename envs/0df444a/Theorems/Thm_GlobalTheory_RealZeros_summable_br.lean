-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_summable_br
-- name    : GlobalTheory.RealZeros.summable_br
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:38.496357+00:00
-- url     : https://prove2.me/theorems/d6dba263-3c21-4316-a861-6776bced806d
-- title:
--   Real Zeros: summable br
-- statement:
--   The Real Zeros construction uses the summable br property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L60-L63

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

theorem GlobalTheory.RealZeros.summable_br {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) {s : ℂ}
    (hs : 0 < s.re) : Summable fun k => br N c d k s := by sorry
