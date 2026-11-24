-- Prove2me | Theorems.Thm_GlobalTheory_exists_minimal_local_generators
-- name    : GlobalTheory.exists_minimal_local_generators
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:35:40.026735+00:00
-- url     : https://prove2.me/theorems/342dd557-bbb5-487c-a99f-55e614345896
-- title:
--   Global Theory: exists minimal local generators
-- statement:
--   The Global Theory construction uses the exists minimal local generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMinimalLocalGenerators.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMinimalLocalGenerators.lean#L34-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulMemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_minimal_local_generators :
    ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (Q : Ideal S) [Q.IsPrime],
      ∃ (h : ℕ) (f : Fin h → S) (g : S), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧
        (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
        h = (maximalIdeal (Localization.AtPrime Q)).spanFinrank ∧
        ∀ (a : Fin h → S) (u : S), u ∉ Q → u * ∑ j, a j * f j ∈ Q ^ 2 → ∀ j, a j ∈ Q := by sorry
