-- Prove2me | Theorems.Thm_GlobalTheory_T_coinvariant_of_locally_constant_twist
-- name    : GlobalTheory.T.coinvariant_of_locally_constant_twist
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:30:31.82406+00:00
-- url     : https://prove2.me/theorems/6e104627-c324-47e1-b5b5-463e2a1ba1d7
-- title:
--   T: coinvariant of locally constant twist
-- statement:
--   The T construction uses the coinvariant of locally constant twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoinvariantOfLocallyConstantTwistStatement.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoinvariantOfLocallyConstantTwistStatement.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoinvariantOfLocallyConstantTwist
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoinvariantOfLocallyConstantTwistStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coinvariant_of_locally_constant_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (R : Finset (GL (Fin a) k)),
    Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) → IsLocallyConstant χ →
    (∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y) →
    (∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) → Φ ∈ coinv ν β a (a + b) := by sorry
