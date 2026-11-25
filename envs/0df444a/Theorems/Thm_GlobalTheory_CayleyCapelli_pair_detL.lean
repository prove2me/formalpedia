-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_pair_detL
-- name    : GlobalTheory.CayleyCapelli.pair_detL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:22.793567+00:00
-- url     : https://prove2.me/theorems/d517ea88-a218-4330-b217-c80c2da6eb21
-- title:
--   Cayley Capelli: pair det L
-- statement:
--   The Cayley Capelli construction uses the pair det L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L83-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L83-L99

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

theorem GlobalTheory.CayleyCapelli.pair_detL (n : ℕ) (P : MvPolynomial (PVar n) C) (Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * detL C n) (rename Sum.inl Q) = pair P (rename Sum.inl (cayOp n C Q)) := by sorry
