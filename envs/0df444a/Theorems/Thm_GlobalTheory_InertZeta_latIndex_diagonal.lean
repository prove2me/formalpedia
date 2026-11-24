-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_latIndex_diagonal
-- name    : GlobalTheory.InertZeta.latIndex_diagonal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:18:22.537683+00:00
-- url     : https://prove2.me/theorems/1700eb0a-0969-4cae-bf6c-fdbd3fcf2700
-- title:
--   Inert Zeta: lat Index diagonal
-- statement:
--   The Inert Zeta construction uses the lat Index diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean#L114-L117

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.InertZeta.latIndex_diagonal {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : Fin n → ℕ) :
    (intV L n).relIndex (preLat (Matrix.diagonal fun i => ϖ ^ d i)) = q ^ (2 * ∑ i, d i) := by sorry
