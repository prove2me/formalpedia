-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_kDel_kD
-- name    : GlobalTheory.CompanionTheory.KDelFormula.kDel_kD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:27.664882+00:00
-- url     : https://prove2.me/theorems/28218ee3-8cdd-4733-a31a-3eaa2e64027d
-- title:
--   KDel Formula: k Del k D
-- statement:
--   The KDel Formula construction uses the k Del k D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RemoveNthSuccVecCons.lean#L48-L55

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

theorem GlobalTheory.CompanionTheory.KDelFormula.kDel_kD {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ}
    (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P) :
    kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) -
      ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) := by sorry
