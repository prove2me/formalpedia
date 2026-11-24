-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_padicAlgCl
-- name    : GroundTheory.PAdicHodge.norm_natCast_padicAlgCl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:02.097174+00:00
-- url     : https://prove2.me/theorems/1a881840-60bc-4b12-8f30-614ef94110f0
-- title:
--   PAdic Hodge: norm nat Cast padic Alg Cl
-- statement:
--   The PAdic Hodge construction uses the norm nat Cast padic Alg Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L61-L70

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

theorem GroundTheory.PAdicHodge.norm_natCast_padicAlgCl {n : ℕ} (hn : n ≠ 0) :
    ‖(n : PadicAlgCl p)‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by sorry
