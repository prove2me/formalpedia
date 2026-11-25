-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_pow_prime_pow
-- name    : GlobalTheory.Cyc.LiftExp.norm_pow_prime_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:20.931949+00:00
-- url     : https://prove2.me/theorems/97722d6b-5185-4d7b-b4ab-2b643d8566ba
-- title:
--   Lift Exp: norm pow prime pow
-- statement:
--   The Lift Exp construction uses the norm pow prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L88-L96

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

theorem GlobalTheory.Cyc.LiftExp.norm_pow_prime_pow (a : ℕ) (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ (l ^ a) - 1‖ = (l : ℝ) ^ (-((j + a : ℕ) : ℤ)) := by sorry
