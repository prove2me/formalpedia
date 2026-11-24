-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_hAct_dosetInd_eq
-- name    : GlobalTheory.InertZeta.hAct_dosetInd_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:22.127122+00:00
-- url     : https://prove2.me/theorems/01ca57ca-e3b8-4861-a4ab-3d2b91a4c819
-- title:
--   Inert Zeta: h Act doset Ind eq
-- statement:
--   The Inert Zeta construction uses the h Act doset Ind eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BiInvariantReplaceSameDoubleCosetSums.lean#L49-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BiInvariantReplaceSameDoubleCosetSums.lean#L49-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
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
open GlobalTheory GlobalTheory.InertZeta
open Formalism.UG
variable {G : Type} [Group G] {K : Subgroup G}

theorem GlobalTheory.InertZeta.hAct_dosetInd_eq (hK : IsCommensurated K) (x₀ : G ⧸ K) (v : G → ℂ) :
    hAct K (dosetInd ℂ K x₀.out) v 1 = ∑' y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, v y.1.out := by sorry
