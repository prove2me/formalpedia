-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_pairing_tateMap
-- name    : GlobalTheory.PDivGroup.pairing_tateMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:27.426732+00:00
-- url     : https://prove2.me/theorems/e42fd58f-93bc-4147-a7e7-b3f1081aa52f
-- title:
--   PDiv Group: pairing tate Map
-- statement:
--   The PDiv Group construction uses the pairing tate Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1098-L1100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1098-L1100

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
variable {G H : PDivGroup p O}
variable [Fact p.Prime]
variable {B : Type} [CommRing B] [Algebra O B]

theorem GlobalTheory.PDivGroup.pairing_tateMap (f : G ⟶ H) (t : G.TateOver B) (χ : H.dual.Tate) :
    pairing H B (tateMap G H B f t) χ = pairing G B t (tateMap _ _ O (dualHom G H f) χ) := by sorry
