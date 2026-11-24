-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_levi_mul_apply_last
-- name    : GlobalTheory.InertZeta.levi_mul_apply_last
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:19:03.002446+00:00
-- url     : https://prove2.me/theorems/0ba2f35b-38a2-4b9f-a327-057153b9672f
-- title:
--   Inert Zeta: levi mul apply last
-- statement:
--   The Inert Zeta construction uses the levi mul apply last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryIwasawaCellsDisjoint.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryIwasawaCellsDisjoint.lean#L32-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCellsDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.InertZeta.levi_mul_apply_last {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) (Fin.last (N + 1)) j = mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * M (Fin.last (N + 1)) j := by sorry
