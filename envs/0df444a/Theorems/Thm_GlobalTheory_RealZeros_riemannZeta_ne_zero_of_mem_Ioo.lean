-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_riemannZeta_ne_zero_of_mem_Ioo
-- name    : GlobalTheory.RealZeros.riemannZeta_ne_zero_of_mem_Ioo
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:18:28.271455+00:00
-- url     : https://prove2.me/theorems/d86f8536-e2c9-4906-94b4-74596458086b
-- title:
--   Real Zeros: riemann Zeta ne zero of mem Ioo
-- statement:
--   The Real Zeros construction uses the riemann Zeta ne zero of mem Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L150-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L150-L163

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

theorem GlobalTheory.RealZeros.riemannZeta_ne_zero_of_mem_Ioo (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := by sorry
