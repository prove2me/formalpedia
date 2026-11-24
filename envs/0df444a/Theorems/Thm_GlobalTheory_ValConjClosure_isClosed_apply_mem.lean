-- Prove2me | Theorems.Thm_GlobalTheory_ValConjClosure_isClosed_apply_mem
-- name    : GlobalTheory.ValConjClosure.isClosed_apply_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:52:03.00762+00:00
-- url     : https://prove2.me/theorems/3716d1ae-4834-48b8-bae1-d36a85b15a58
-- title:
--   Val Conj Closure: is Closed apply mem
-- statement:
--   The Val Conj Closure construction uses the is Closed apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsConjOverPrime.lean#L66-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsConjOverPrime.lean#L66-L90

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

theorem GlobalTheory.ValConjClosure.isClosed_apply_mem {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
    (x : Ω) (T : Set Ω) : IsClosed {σ : Ω ≃ₐ[F] Ω | σ x ∈ T} := by sorry
