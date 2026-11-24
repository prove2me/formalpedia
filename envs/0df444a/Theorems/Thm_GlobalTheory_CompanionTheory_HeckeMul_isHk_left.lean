-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_isHk_left
-- name    : GlobalTheory.CompanionTheory.HeckeMul.isHk_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:51.427254+00:00
-- url     : https://prove2.me/theorems/82227ada-206d-4b5f-a1ea-e1ec6d79cb28
-- title:
--   Hecke Mul: is Hk left
-- statement:
--   The Hecke Mul construction uses the is Hk left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L53-L55

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

theorem GlobalTheory.CompanionTheory.HeckeMul.isHk_left {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (k * x) = e x := by sorry
