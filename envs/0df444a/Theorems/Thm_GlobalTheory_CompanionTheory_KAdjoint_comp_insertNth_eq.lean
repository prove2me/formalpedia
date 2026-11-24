-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KAdjoint_comp_insertNth_eq
-- name    : GlobalTheory.CompanionTheory.KAdjoint.comp_insertNth_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:16.556093+00:00
-- url     : https://prove2.me/theorems/162618de-85f1-4aba-ad3f-f782dca825e9
-- title:
--   KAdjoint: comp insert Nth eq
-- statement:
--   The KAdjoint construction uses the comp insert Nth eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompInsertNthEq.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompInsertNthEq.lean#L11-L16

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

theorem GlobalTheory.CompanionTheory.KAdjoint.comp_insertNth_eq {m : ℕ} (b : β → P) (s : Fin (m + 1)) (i : β) (J : Fin m → β) :
    b ∘ (s.insertNth i J : Fin (m + 1) → β) = s.insertNth (b i) (b ∘ J) := by sorry
