-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_rpow_axExponent_mono
-- name    : GroundTheory.PAdicHodge.rpow_axExponent_mono
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:32.056277+00:00
-- url     : https://prove2.me/theorems/d657c0f1-d3bf-41d5-a895-2bc4c87bb82b
-- title:
--   PAdic Hodge: rpow ax Exponent mono
-- statement:
--   The PAdic Hodge construction uses the rpow ax Exponent mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L317-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L317-L319

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

theorem GroundTheory.PAdicHodge.rpow_axExponent_mono {j k : ℕ} (h : j ≤ k) :
    (p : ℝ) ^ axExponent p j ≤ (p : ℝ) ^ axExponent p k := by sorry
