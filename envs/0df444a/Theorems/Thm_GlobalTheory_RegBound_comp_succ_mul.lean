-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_comp_succ_mul
-- name    : GlobalTheory.RegBound.comp_succ_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:19.566813+00:00
-- url     : https://prove2.me/theorems/209018b0-40e2-4150-a78d-81efb8031fec
-- title:
--   Reg Bound: comp succ mul
-- statement:
--   The Reg Bound construction uses the comp succ mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L22-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]

theorem GlobalTheory.RegBound.comp_succ_mul {h : MvPolynomial σ K} (hh : h.IsHomogeneous 1) (e : ℕ)
    (B : MvPolynomial σ K) :
    homogeneousComponent (e + 1) (h * B) = h * homogeneousComponent e B := by sorry
