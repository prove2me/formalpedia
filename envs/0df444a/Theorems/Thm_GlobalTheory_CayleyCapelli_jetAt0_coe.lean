-- Prove2me | Theorems.Thm_GlobalTheory_CayleyCapelli_jetAt0_coe
-- name    : GlobalTheory.CayleyCapelli.jetAt0_coe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:55.644288+00:00
-- url     : https://prove2.me/theorems/0e6e169d-7852-45a5-adbf-0beed911838e
-- title:
--   Cayley Capelli: jet At0 coe
-- statement:
--   The Cayley Capelli construction uses the jet At0 coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdIccMulFactorial.lean#L22-L26

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

theorem GlobalTheory.CayleyCapelli.jetAt0_coe (P Q : MvPolynomial σ C) :
    jetAt0 P (Q : MvPowerSeries σ C) = pair P Q := by sorry
