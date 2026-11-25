-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_res_comp_mulP
-- name    : GlobalTheory.PDivGroup.res_comp_mulP
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:28:16.197776+00:00
-- url     : https://prove2.me/theorems/dc31b354-3971-4820-9e08-97e66950fd11
-- title:
--   PDiv Group: res comp mul P
-- statement:
--   The PDiv Group construction uses the res comp mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L89-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (G : PDivGroup p O)

theorem GlobalTheory.PDivGroup.res_comp_mulP (n : ℕ) : (G.res n).comp (G.mulP n) = mulBy O _ p := by sorry
