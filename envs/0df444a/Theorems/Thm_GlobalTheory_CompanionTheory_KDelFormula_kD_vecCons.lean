-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_kD_vecCons
-- name    : GlobalTheory.CompanionTheory.KDelFormula.kD_vecCons
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:24.817082+00:00
-- url     : https://prove2.me/theorems/141fe842-8df8-45e8-ab0d-a6af01f40368
-- title:
--   KDel Formula: k D vec Cons
-- statement:
--   The KDel Formula construction uses the k D vec Cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L29-L46

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

theorem GlobalTheory.CompanionTheory.KDelFormula.kD_vecCons (T : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (x : P)
    (Y : Fin q → P) :
    kD T η (Matrix.vecCons x Y) =
      T x (η Y) - ∑ t, T (Y t) (η (Function.update Y t x)) := by sorry
