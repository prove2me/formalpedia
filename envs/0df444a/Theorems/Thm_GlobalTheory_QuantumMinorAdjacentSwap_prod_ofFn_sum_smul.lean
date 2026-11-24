-- Prove2me | Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_prod_ofFn_sum_smul
-- name    : GlobalTheory.QuantumMinorAdjacentSwap.prod_ofFn_sum_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:39.548828+00:00
-- url     : https://prove2.me/theorems/afa31965-7d0f-4f41-9e3a-681db96ac073
-- title:
--   Quantum Minor Adjacent Swap: prod of Fn sum smul
-- statement:
--   The Quantum Minor Adjacent Swap construction uses the prod of Fn sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L13-L20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.QuantumMinorAdjacentSwap.prod_ofFn_sum_smul {n : ℕ} {ι : Type} [Fintype ι] (a : Fin n → ι → ℂ)
    (T : Fin n → ι → A) :
    (List.ofFn fun k => ∑ c, a k c • T k c).prod =
      ∑ c : Fin n → ι, (∏ k, a k (c k)) • (List.ofFn fun k => T k (c k)).prod := by sorry
