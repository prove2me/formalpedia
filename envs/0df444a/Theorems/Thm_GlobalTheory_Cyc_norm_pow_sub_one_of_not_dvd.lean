-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_norm_pow_sub_one_of_not_dvd
-- name    : GlobalTheory.Cyc.norm_pow_sub_one_of_not_dvd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:10.169815+00:00
-- url     : https://prove2.me/theorems/4b908c1a-bbc3-5f3c-a359-beb4584c34bf
-- title:
--   Cyc: norm pow sub one of not dvd
-- statement:
--   The Cyc construction uses the norm pow sub one of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L27-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L27-L42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.Cyc.norm_pow_sub_one_of_not_dvd (x : ℤ_[l]) (hx : ‖x - 1‖ < 1) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖x ^ n - 1‖ = ‖x - 1‖ := by sorry
