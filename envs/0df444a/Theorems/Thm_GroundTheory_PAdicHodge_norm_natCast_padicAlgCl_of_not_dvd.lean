-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_padicAlgCl_of_not_dvd
-- name    : GroundTheory.PAdicHodge.norm_natCast_padicAlgCl_of_not_dvd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:17.685388+00:00
-- url     : https://prove2.me/theorems/92f9d745-3175-49d2-8c4a-bfca02e34b42
-- title:
--   PAdic Hodge: norm nat Cast padic Alg Cl of not dvd
-- statement:
--   The PAdic Hodge construction uses the norm nat Cast padic Alg Cl of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L72-L76

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

theorem GroundTheory.PAdicHodge.norm_natCast_padicAlgCl_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) :
    ‖(n : PadicAlgCl p)‖ = 1 := by sorry
