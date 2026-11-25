-- Prove2me | Theorems.Thm_GlobalTheory_TensOp_core
-- name    : GlobalTheory.TensOp.core
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:04:56.82883+00:00
-- url     : https://prove2.me/theorems/8b9d9566-2911-49e7-819a-7e5e3bf38a6d
-- title:
--   Tens Op: core
-- statement:
--   The Tens Op construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeTensorOperatorRaise.lean#L49-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeTensorOperatorRaise.lean#L49-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.TensOp

theorem GlobalTheory.TensOp.core (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (N ι : Type) [NormedAddCommGroup N]
    [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N)
    (φ : ι → V →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ) (hE : KUnit ε E) (hF : KUnit ε F)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a)
    (hAs : ∀ x : ι → V, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0)
      ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2)
    (hφ : ∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w)
    (hb : ∀ x : V, (∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0) ≤ c ^ 2 * ‖x‖ ^ 2)
    (w : V) (j : ι) : CasKLe ε F (c + s) (φ j w) := by sorry
