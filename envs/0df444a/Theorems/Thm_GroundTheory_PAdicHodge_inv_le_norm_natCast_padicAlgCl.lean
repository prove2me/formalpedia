-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_inv_le_norm_natCast_padicAlgCl
-- name    : GroundTheory.PAdicHodge.inv_le_norm_natCast_padicAlgCl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:46.670683+00:00
-- url     : https://prove2.me/theorems/5d226047-30af-4926-aff9-edcbdaba4d90
-- title:
--   PAdic Hodge: inv le norm nat Cast padic Alg Cl
-- statement:
--   The PAdic Hodge construction uses the inv le norm nat Cast padic Alg Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L78-L85

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
variable {p : ℕ} [hp : Fact p.Prime]

theorem GroundTheory.PAdicHodge.inv_le_norm_natCast_padicAlgCl {n : ℕ} (hn : n ≠ 0) (h : ¬ p ^ 2 ∣ n) :
    (p : ℝ)⁻¹ ≤ ‖(n : PadicAlgCl p)‖ := by sorry
