-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_axExponent_succ
-- name    : GroundTheory.PAdicHodge.axExponent_succ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:35.470533+00:00
-- url     : https://prove2.me/theorems/9c2d580b-8456-4d73-b08b-51ee860fe3d3
-- title:
--   PAdic Hodge: ax Exponent succ
-- statement:
--   The PAdic Hodge construction uses the ax Exponent succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L285-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L285-L293

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
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
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.axExponent_succ (k : ℕ) :
    axExponent p (k + 1) = axExponent p k + 1 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by sorry
