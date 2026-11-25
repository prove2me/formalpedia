-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_detL_eq
-- name    : GlobalTheory.CayleyCapelli.detL_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:55.197337+00:00
-- url     : https://prove2.me/theorems/944c2846-ff58-4b78-b77d-a7d59cbcc3d2
-- title:
--   Cayley Capelli: det L eq
-- statement:
--   The Cayley Capelli construction uses the det L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L64-L68

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

theorem GlobalTheory.CayleyCapelli.detL_eq (n : ℕ) : detL C n = rename Sum.inl (cayDet n C) := by sorry
