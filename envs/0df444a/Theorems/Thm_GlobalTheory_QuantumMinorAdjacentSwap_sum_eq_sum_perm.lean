-- Prove2me | Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_sum_eq_sum_perm
-- name    : GlobalTheory.QuantumMinorAdjacentSwap.sum_eq_sum_perm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:01.745149+00:00
-- url     : https://prove2.me/theorems/f2305011-f80b-4f02-9e35-970055657d9c
-- title:
--   Quantum Minor Adjacent Swap: sum eq sum perm
-- statement:
--   The Quantum Minor Adjacent Swap construction uses the sum eq sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L174-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L174-L185

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
open Formalism.REAL

theorem GlobalTheory.QuantumMinorAdjacentSwap.sum_eq_sum_perm {n : ℕ} {V : Type} [AddCommMonoid V] (F : (Fin n → Fin n) → V)
    (hF : ∀ d, ¬ Function.Injective d → F d = 0) :
    ∑ d, F d = ∑ σ : Equiv.Perm (Fin n), F σ := by sorry
