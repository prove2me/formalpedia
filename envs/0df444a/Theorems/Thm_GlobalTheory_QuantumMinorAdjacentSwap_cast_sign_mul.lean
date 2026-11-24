-- Prove2me | Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_cast_sign_mul
-- name    : GlobalTheory.QuantumMinorAdjacentSwap.cast_sign_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:54.320824+00:00
-- url     : https://prove2.me/theorems/567dc97f-1e56-4744-bfd4-3a821d430472
-- title:
--   Quantum Minor Adjacent Swap: cast sign mul
-- statement:
--   The Quantum Minor Adjacent Swap construction uses the cast sign mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L103-L105

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

theorem GlobalTheory.QuantumMinorAdjacentSwap.cast_sign_mul {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : A) :
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * x = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • x := by sorry
