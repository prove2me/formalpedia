-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_prod_exp_eq
-- name    : GlobalTheory.InertZeta.prod_exp_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:26.127632+00:00
-- url     : https://prove2.me/theorems/46916dc0-34c8-45e9-bbe2-7c88986abcce
-- title:
--   Inert Zeta: prod exp eq
-- statement:
--   The Inert Zeta construction uses the prod exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixLengthExistsOfElementaryDivisors.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixLengthExistsOfElementaryDivisors.lean#L10-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.InertZeta

theorem GlobalTheory.InertZeta.prod_exp_eq {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by sorry
