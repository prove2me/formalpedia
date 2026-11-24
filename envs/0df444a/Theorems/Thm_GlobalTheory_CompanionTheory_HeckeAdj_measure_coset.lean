-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_measure_coset
-- name    : GlobalTheory.CompanionTheory.HeckeAdj.measure_coset
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:35.144518+00:00
-- url     : https://prove2.me/theorems/4f6dcf47-d182-43af-b1f3-28f240f808bf
-- title:
--   Hecke Adj: measure coset
-- statement:
--   The Hecke Adj construction uses the measure coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L27-L34

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.CompanionTheory.HeckeAdj.measure_coset (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (q : G ⧸ K) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) = μ (K : Set G) := by sorry
