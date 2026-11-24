-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_axExponent_mono
-- name    : GroundTheory.PAdicHodge.axExponent_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:11.33629+00:00
-- url     : https://prove2.me/theorems/e5ed7aea-388e-4962-b7d2-c111d8cceb53
-- title:
--   PAdic Hodge: ax Exponent mono
-- statement:
--   The PAdic Hodge construction uses the ax Exponent mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L302-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L302-L308

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

theorem GroundTheory.PAdicHodge.axExponent_mono {j k : ℕ} (h : j ≤ k) : axExponent p j ≤ axExponent p k := by sorry
