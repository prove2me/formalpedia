-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_pair_diffOp
-- name    : GlobalTheory.CayleyCapelli.pair_diffOp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:36.178811+00:00
-- url     : https://prove2.me/theorems/953508d8-b9cf-47d1-9454-7a5e0ad18821
-- title:
--   Cayley Capelli: pair diff Op
-- statement:
--   The Cayley Capelli construction uses the pair diff Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L28-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L28-L55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]

theorem GlobalTheory.CayleyCapelli.pair_diffOp [CharZero C] (B : σ →₀ ℕ) (P Q : MvPolynomial σ C) :
    pair (monomial B (1 : C)) (diffOp P Q) = pair (monomial B (1 : C) * P) Q := by sorry
