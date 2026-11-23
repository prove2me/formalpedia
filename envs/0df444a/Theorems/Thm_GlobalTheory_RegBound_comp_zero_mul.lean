-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_comp_zero_mul
-- name    : GlobalTheory.RegBound.comp_zero_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:07.587932+00:00
-- url     : https://prove2.me/theorems/155076a5-3e81-431a-8d2a-6901c407c943
-- title:
--   Reg Bound: comp zero mul
-- statement:
--   The Reg Bound construction uses the comp zero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L34-L40

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

theorem GlobalTheory.RegBound.comp_zero_mul {h : MvPolynomial σ K} (hh : h.IsHomogeneous 1)
    (B : MvPolynomial σ K) : homogeneousComponent 0 (h * B) = 0 := by sorry
