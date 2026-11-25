-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_wt_eq
-- name    : GlobalTheory.CayleyCapelli.wt_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:56.724475+00:00
-- url     : https://prove2.me/theorems/34ed5ca8-d340-443a-8593-212a1f4f047e
-- title:
--   Cayley Capelli: wt eq
-- statement:
--   The Cayley Capelli construction uses the wt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L15-L16

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

theorem GlobalTheory.CayleyCapelli.wt_eq (A : σ →₀ ℕ) : wt C A = (mfact A : C) := by sorry
