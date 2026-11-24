-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_one_le_rpow_axExponent
-- name    : GroundTheory.PAdicHodge.one_le_rpow_axExponent
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:13.065687+00:00
-- url     : https://prove2.me/theorems/5bde2f02-3c07-457d-a325-3ddc2122ae36
-- title:
--   PAdic Hodge: one le rpow ax Exponent
-- statement:
--   The PAdic Hodge construction uses the one le rpow ax Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L314-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L314-L315

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

theorem GroundTheory.PAdicHodge.one_le_rpow_axExponent (k : ℕ) : 1 ≤ (p : ℝ) ^ axExponent p k := by sorry
