-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_mfact_ne_zero
-- name    : GlobalTheory.CayleyCapelli.mfact_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:00.541481+00:00
-- url     : https://prove2.me/theorems/30d618a0-9ead-4a4c-87ef-5953736bd7fb
-- title:
--   Cayley Capelli: mfact ne zero
-- statement:
--   The Cayley Capelli construction uses the mfact ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L18-L20

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

theorem GlobalTheory.CayleyCapelli.mfact_ne_zero [CharZero C] (A : σ →₀ ℕ) : (mfact A : C) ≠ 0 := by sorry
