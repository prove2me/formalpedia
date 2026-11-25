-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KAdjoint_position_sum
-- name    : GlobalTheory.CompanionTheory.KAdjoint.position_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:08.046472+00:00
-- url     : https://prove2.me/theorems/d6521d50-54dd-476d-8487-2de01e5a39cd
-- title:
--   KAdjoint: position sum
-- statement:
--   The KAdjoint construction uses the position sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompInsertNthEq.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompInsertNthEq.lean#L18-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KAdjoint
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]

theorem GlobalTheory.CompanionTheory.KAdjoint.position_sum (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) (s : Fin (m + 1)) :
    ∑ I : Fin (m + 1) → β,
        B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
      = kIp B b η (kDel T' b θ) := by sorry
