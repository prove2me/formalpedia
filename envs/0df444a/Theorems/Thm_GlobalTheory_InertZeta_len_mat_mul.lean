-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_len_mat_mul
-- name    : GlobalTheory.InertZeta.len_mat_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:28:44.617644+00:00
-- url     : https://prove2.me/theorems/3f982736-2d27-4cf7-9927-bf48088de655
-- title:
--   Inert Zeta: len mat mul
-- statement:
--   The Inert Zeta construction uses the len mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L90-L93

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.InertZeta.len_mat_mul {σ : L →+* L} {a b : GU σ n} (ha : a ∈ KU σ n) (hb : b ∈ KU σ n) (g : GU σ n) :
    len (mat (a * g * b)) = len (mat g) := by sorry
