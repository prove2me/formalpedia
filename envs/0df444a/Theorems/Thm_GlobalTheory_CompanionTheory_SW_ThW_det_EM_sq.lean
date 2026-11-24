-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_det_EM_sq
-- name    : GlobalTheory.CompanionTheory.SW.ThW.det_EM_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:11:24.526297+00:00
-- url     : https://prove2.me/theorems/cc9bb0fe-fd9b-44b8-89e5-f77aeec52bac
-- title:
--   Th W: det EM sq
-- statement:
--   The Th W construction uses the det EM sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeMatrixDeterminantFormula.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeMatrixDeterminantFormula.lean#L14-L36

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeMatrixDeterminantFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker nonZeroDivisors
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq (InfinitePlace F)]

theorem GlobalTheory.CompanionTheory.SW.ThW.det_EM_sq {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) :
    (EM ρ (fun v => b v)).det ^ 2 = (discr F : ℝ) := by sorry
