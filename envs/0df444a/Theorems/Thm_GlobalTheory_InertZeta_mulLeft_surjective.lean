-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_mulLeft_surjective
-- name    : GlobalTheory.InertZeta.mulLeft_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:20:25.442673+00:00
-- url     : https://prove2.me/theorems/972bcadd-8926-44fd-a645-53493b8208d5
-- title:
--   Inert Zeta: mul Left surjective
-- statement:
--   The Inert Zeta construction uses the mul Left surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L50-L51

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

theorem GlobalTheory.InertZeta.mulLeft_surjective {c : L} (hc : c ≠ 0) : Function.Surjective (AddMonoidHom.mulLeft c) := by sorry
