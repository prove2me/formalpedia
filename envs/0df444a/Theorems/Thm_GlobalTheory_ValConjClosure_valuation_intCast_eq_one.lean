-- Prove2me | Theorems.Thm_GlobalTheory_ValConjClosure_valuation_intCast_eq_one
-- name    : GlobalTheory.ValConjClosure.valuation_intCast_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:50:42.564847+00:00
-- url     : https://prove2.me/theorems/a9c025ae-67ce-436f-9aa1-f475e49ab42d
-- title:
--   Val Conj Closure: valuation int Cast eq one
-- statement:
--   The Val Conj Closure construction uses the valuation int Cast eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsConjOverPrime.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsConjOverPrime.lean#L11-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsConjOverPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
open GlobalTheory GlobalTheory.ValConjClosure

theorem GlobalTheory.ValConjClosure.valuation_intCast_eq_one {Ω : Type} [Field Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : A.valuation (n : Ω) = 1 := by sorry
