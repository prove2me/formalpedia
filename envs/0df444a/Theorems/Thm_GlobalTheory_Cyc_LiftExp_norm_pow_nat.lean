-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_pow_nat
-- name    : GlobalTheory.Cyc.LiftExp.norm_pow_nat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:27.34766+00:00
-- url     : https://prove2.me/theorems/f92048f3-bc91-4264-b90a-2fadeecf0755
-- title:
--   Lift Exp: norm pow nat
-- statement:
--   The Lift Exp construction uses the norm pow nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L98-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L98-L107

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.LiftExp
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.Cyc.LiftExp.norm_pow_nat (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (n : ℕ) (hn : n ≠ 0) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValNat l n : ℤ))) := by sorry
