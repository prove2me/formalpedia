-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_pair_detL_pow
-- name    : GlobalTheory.CayleyCapelli.pair_detL_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:15.675459+00:00
-- url     : https://prove2.me/theorems/a1c973a8-ecc8-4e9f-928b-659579a9b225
-- title:
--   Cayley Capelli: pair det L pow
-- statement:
--   The Cayley Capelli construction uses the pair det L pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L101-L106

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

theorem GlobalTheory.CayleyCapelli.pair_detL_pow (n s : ℕ) (P : MvPolynomial (PVar n) C) :
    pair (P * detL C n) (detL C n ^ (s + 1)) =
      ((∏ c ∈ Finset.range n, (s + 1 + c) : ℕ) : C) * pair P (detL C n ^ s) := by sorry
