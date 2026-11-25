-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_cycloChar_sub_one_le
-- name    : GroundTheory.PAdicHodge.norm_cycloChar_sub_one_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:54.76487+00:00
-- url     : https://prove2.me/theorems/af1b1029-b987-479d-848a-8da52075aafe
-- title:
--   PAdic Hodge: norm cyclo Char sub one le
-- statement:
--   The PAdic Hodge construction uses the norm cyclo Char sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L116-L120

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem GroundTheory.PAdicHodge.norm_cycloChar_sub_one_le (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    ‖(cycloChar K σ : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by sorry
