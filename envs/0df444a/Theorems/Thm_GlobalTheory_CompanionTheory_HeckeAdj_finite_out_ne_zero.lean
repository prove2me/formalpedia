-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_finite_out_ne_zero
-- name    : GlobalTheory.CompanionTheory.HeckeAdj.finite_out_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:16.010436+00:00
-- url     : https://prove2.me/theorems/9e5a1cec-a3f6-4d16-aaef-8e9b7f53c346
-- title:
--   Hecke Adj: finite out ne zero
-- statement:
--   The Hecke Adj construction uses the finite out ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L17-L23

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

theorem GlobalTheory.CompanionTheory.HeckeAdj.finite_out_ne_zero (K : Subgroup G) (hKo : IsOpen (K : Set G)) {φ : G → ℂ} (hφ : HasCompactSupport φ) :
    {q : G ⧸ K | φ q.out ≠ 0}.Finite := by sorry
