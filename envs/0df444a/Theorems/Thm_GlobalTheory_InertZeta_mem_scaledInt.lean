-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_mem_scaledInt
-- name    : GlobalTheory.InertZeta.mem_scaledInt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:56:10.807696+00:00
-- url     : https://prove2.me/theorems/5615c499-9e9f-4107-9c85-bd945fca43e7
-- title:
--   Inert Zeta: mem scaled Int
-- statement:
--   The Inert Zeta construction uses the mem scaled Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L48-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L48-L48

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

theorem GlobalTheory.InertZeta.mem_scaledInt {c x : L} : x ∈ scaledInt c ↔ c * x ∈ intL L := by sorry
