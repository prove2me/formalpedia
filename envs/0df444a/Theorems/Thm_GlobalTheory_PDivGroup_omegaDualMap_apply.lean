-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_omegaDualMap_apply
-- name    : GlobalTheory.PDivGroup.omegaDualMap_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:56.586799+00:00
-- url     : https://prove2.me/theorems/7eba8bb5-5802-497a-98e5-908bb5e0c9e0
-- title:
--   PDiv Group: omega Dual Map apply
-- statement:
--   The PDiv Group construction uses the omega Dual Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L614-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L614-L615

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
variable (G H K : PDivGroup p O)
variable [Fact p.Prime]
variable {G H K}

theorem GlobalTheory.PDivGroup.omegaDualMap_apply (f : G ⟶ H) :
    omegaDualMap G H f = omegaMap H.dual G.dual (dualHom G H f) := by sorry
