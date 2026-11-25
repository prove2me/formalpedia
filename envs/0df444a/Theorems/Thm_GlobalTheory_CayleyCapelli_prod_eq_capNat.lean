-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_prod_eq_capNat
-- name    : GlobalTheory.CayleyCapelli.prod_eq_capNat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:09.254841+00:00
-- url     : https://prove2.me/theorems/d15263ff-27b6-4cff-8cc9-b477da5854a9
-- title:
--   Cayley Capelli: prod eq cap Nat
-- statement:
--   The Cayley Capelli construction uses the prod eq cap Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L135-L139

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

theorem GlobalTheory.CayleyCapelli.prod_eq_capNat (n x : ℕ) :
    (∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n, (t + c)) = capNat n x := by sorry
