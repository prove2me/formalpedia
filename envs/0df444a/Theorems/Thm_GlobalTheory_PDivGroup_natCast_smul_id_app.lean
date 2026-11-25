-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_natCast_smul_id_app
-- name    : GlobalTheory.PDivGroup.natCast_smul_id_app
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:05:43.589186+00:00
-- url     : https://prove2.me/theorems/3034a315-8329-5bf5-a50a-fca210c33602
-- title:
--   PDiv Group: nat Cast smul id app
-- statement:
--   The PDiv Group construction uses the nat Cast smul id app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L269-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L269-L271

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
variable {G H K : PDivGroup p O}
variable [Fact p.Prime]

theorem GlobalTheory.PDivGroup.natCast_smul_id_app (G : PDivGroup p O) (k n : ℕ) :
    Hom.app ((k : ℤ_[p]) • 𝟙 G) n = mulBy O _ k := by sorry
