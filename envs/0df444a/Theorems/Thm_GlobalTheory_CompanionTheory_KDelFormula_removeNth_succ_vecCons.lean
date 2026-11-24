-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_removeNth_succ_vecCons
-- name    : GlobalTheory.CompanionTheory.KDelFormula.removeNth_succ_vecCons
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:24.876597+00:00
-- url     : https://prove2.me/theorems/b53d4c06-8f7e-4524-82d3-bf8571d862d6
-- title:
--   KDel Formula: remove Nth succ vec Cons
-- statement:
--   The KDel Formula construction uses the remove Nth succ vec Cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L11-L16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KDelFormula
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem GlobalTheory.CompanionTheory.KDelFormula.removeNth_succ_vecCons {n : ℕ} (x : P) (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    t.succ.removeNth (Matrix.vecCons x Y) = Matrix.vecCons x (t.removeNth Y) := by sorry
