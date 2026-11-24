-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_hasSum_group
-- name    : GlobalTheory.RealZeros.hasSum_group
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:49.223623+00:00
-- url     : https://prove2.me/theorems/bb4f1df7-f8db-4245-9284-b8c2929c2d14
-- title:
--   Real Zeros: has Sum group
-- statement:
--   The Real Zeros construction uses the has Sum group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L83-L88

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

theorem GlobalTheory.RealZeros.hasSum_group {f : ℕ → ℂ} {a : ℂ} (N : ℕ) [NeZero N] (h : HasSum f a) :
    HasSum (fun k => ∑ j : Fin N, f (N * k + j)) a := by sorry
