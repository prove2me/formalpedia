-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_br_ofReal
-- name    : GlobalTheory.RealZeros.br_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:26.127335+00:00
-- url     : https://prove2.me/theorems/47b60538-af5b-4ffc-b9a1-03cd0d4b9917
-- title:
--   Real Zeros: br of Real
-- statement:
--   The Real Zeros construction uses the br of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L90-L93

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

theorem GlobalTheory.RealZeros.br_ofReal (N c d k : ℕ) (σ : ℝ) :
    br N c d k σ = ((((N * k + c : ℕ) : ℝ) ^ (-σ) - ((N * k + d : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by sorry
