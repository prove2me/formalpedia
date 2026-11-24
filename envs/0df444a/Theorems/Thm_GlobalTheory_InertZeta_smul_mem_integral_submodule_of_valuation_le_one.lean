-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_smul_mem_integral_submodule_of_valuation_le_one
-- name    : GlobalTheory.InertZeta.smul_mem_integral_submodule_of_valuation_le_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:20:00.830234+00:00
-- url     : https://prove2.me/theorems/b45ca619-47b8-4a81-a17f-beb5c9b4fefa
-- title:
--   Inert Zeta: smul mem integral submodule of valuation le one
-- statement:
--   The Inert Zeta construction uses the smul mem integral submodule of valuation le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeAddVectorDetValuation.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeAddVectorDetValuation.lean#L10-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeAddVectorDetValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.InertZeta

theorem GlobalTheory.InertZeta.smul_mem_integral_submodule_of_valuation_le_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {P : Submodule (Formalism.UG.intL L) (Fin n → L)} {x : L} (hx : Valued.v x ≤ 1) {w : Fin n → L} (hw : w ∈ P) :
    x • w ∈ P := by sorry
