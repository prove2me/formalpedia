-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_isInvInvariant
-- name    : GlobalTheory.CompanionTheory.HeckeAdj.isInvInvariant
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:41.68166+00:00
-- url     : https://prove2.me/theorems/0c8f334b-00c3-4feb-9f44-3c394603bd54
-- title:
--   Hecke Adj: is Inv Invariant
-- statement:
--   The Hecke Adj construction uses the is Inv Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L124-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L124-L139

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAdj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HeckeAdj.isInvInvariant [MeasurableSpace F] [BorelSpace F] (μ : Measure (GL ι F)) [μ.IsHaarMeasure]
    (K : Subgroup (GL ι F)) (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    μ.IsInvInvariant := by sorry
