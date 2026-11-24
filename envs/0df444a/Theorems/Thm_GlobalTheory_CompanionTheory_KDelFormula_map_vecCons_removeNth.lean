-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_map_vecCons_removeNth
-- name    : GlobalTheory.CompanionTheory.KDelFormula.map_vecCons_removeNth
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:21.030926+00:00
-- url     : https://prove2.me/theorems/58c0c704-580c-4bf9-857e-3146172ff867
-- title:
--   KDel Formula: map vec Cons remove Nth
-- statement:
--   The KDel Formula construction uses the map vec Cons remove Nth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L18-L27

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

theorem GlobalTheory.CompanionTheory.KDelFormula.map_vecCons_removeNth {n : ℕ} (η : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (x : P)
    (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    η (Matrix.vecCons x (t.removeNth Y)) = (-1 : ℤ) ^ (t : ℕ) • η (Function.update Y t x) := by sorry
