-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
-- name    : GlobalTheory.InertZeta.IsInt.mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:19.149544+00:00
-- url     : https://prove2.me/theorems/5fd847ac-29eb-4185-a061-4ddf8bf8f7b7
-- title:
--   Is Int: mul
-- statement:
--   The Is Int construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L18-L21

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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

theorem GlobalTheory.InertZeta.IsInt.mul {ι κ μ : Type} [Fintype κ] {M : Matrix ι κ L} {N : Matrix κ μ L} (hM : IsInt M) (hN : IsInt N) :
    IsInt (M * N) := by sorry
