-- Prove2me | Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_qminor_comp_perm
-- name    : GlobalTheory.QuantumMinorAdjacentSwap.qminor_comp_perm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:59.56724+00:00
-- url     : https://prove2.me/theorems/8054c4a1-e51e-459a-95ce-3d304b0079ff
-- title:
--   Quantum Minor Adjacent Swap: qminor comp perm
-- statement:
--   The Quantum Minor Adjacent Swap construction uses the qminor comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L141-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L141-L160

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

theorem GlobalTheory.QuantumMinorAdjacentSwap.qminor_comp_perm {n t : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a : Fin t → Fin n) (u : ℂ) (τ : Equiv.Perm (Fin t)) (b : Fin t → Fin n) :
    qminor E a (b ∘ τ) u = (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) • qminor E a b u := by sorry
