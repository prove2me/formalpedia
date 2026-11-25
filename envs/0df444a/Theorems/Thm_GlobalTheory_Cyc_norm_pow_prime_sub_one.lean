-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_norm_pow_prime_sub_one
-- name    : GlobalTheory.Cyc.norm_pow_prime_sub_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:24.831245+00:00
-- url     : https://prove2.me/theorems/6575202a-cc27-4352-84af-435ab69b7504
-- title:
--   Cyc: norm pow prime sub one
-- statement:
--   The Cyc construction uses the norm pow prime sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L44-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneOfNotDvd.lean#L44-L69

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

theorem GlobalTheory.Cyc.norm_pow_prime_sub_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) :
    ‖x ^ l - 1‖ = ‖x - 1‖ * ‖(l : ℤ_[l])‖ := by sorry
