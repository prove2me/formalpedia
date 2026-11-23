-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_support_hconv
-- name    : GlobalTheory.CompanionTheory.HeckeMul.support_hconv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:57.332391+00:00
-- url     : https://prove2.me/theorems/9573ab25-c485-42a4-99c8-402866b8b890
-- title:
--   Hecke Mul: support hconv
-- statement:
--   The Hecke Mul construction uses the support hconv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L57-L68

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HeckeMul.support_hconv (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) :
    Function.support (hconv K e₁ e₂) ⊆ tsupport e₁ * tsupport e₂ := by sorry
