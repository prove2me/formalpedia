-- Prove2me | Theorems.Thm_GlobalTheory_MultipleMembershipForAll_main
-- name    : GlobalTheory.MultipleMembershipForAll.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:58.49053+00:00
-- url     : https://prove2.me/theorems/59f6cd68-2d80-4929-92cd-ccfeecf2afef
-- title:
--   Multiple Membership For All: main
-- statement:
--   The Multiple Membership For All construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulMemOfForall.lean#L36-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulMemOfForall.lean#L36-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulMemOfForall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultipleMembershipForAll
open IsLocalRing

theorem GlobalTheory.MultipleMembershipForAll.main : ∀ (S : Type) [inst : CommRing S] [IsNoetherianRing S] (Q : Ideal S)
    [inst_2 : Ideal.IsPrime Q], ∃ (h : ℕ) (f : Fin h → S), ∃ g ∉ Q, (∀ (j : Fin h), f j ∈ Q) ∧
    (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
    h = Submodule.spanFinrank (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
    ∀ (a : Fin h → S), ∀ u ∉ Q, u * ∑ j : Fin h, a j * f j ∈ Q ^ (2 : ℕ) →
      ∀ (j : Fin h), a j ∈ Q := by sorry
