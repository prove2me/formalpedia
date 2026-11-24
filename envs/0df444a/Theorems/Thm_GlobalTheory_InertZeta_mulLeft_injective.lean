-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_mulLeft_injective
-- name    : GlobalTheory.InertZeta.mulLeft_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:18:25.443611+00:00
-- url     : https://prove2.me/theorems/57f6e805-268e-4ced-9081-f7c556f3293b
-- title:
--   Inert Zeta: mul Left injective
-- statement:
--   The Inert Zeta construction uses the mul Left injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L53-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.InertZeta.mulLeft_injective {c : L} (hc : c ≠ 0) : Function.Injective (AddMonoidHom.mulLeft c) := by sorry
