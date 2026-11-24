-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_exists_open_sub
-- name    : GlobalTheory.CompanionTheory.HeckeInj.exists_open_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:19.977105+00:00
-- url     : https://prove2.me/theorems/77a56c4a-3924-4a08-88fa-d42069310996
-- title:
--   Hecke Inj: exists open sub
-- statement:
--   The Hecke Inj construction uses the exists open sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L149-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L149-L165

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HeckeInj.exists_open_sub {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (s : Finset (GL ι F)) :
    ∃ L : Subgroup (GL ι F), IsOpen (L : Set (GL ι F)) ∧ L ≤ K ∧ ∀ g ∈ s, ∀ l ∈ L, g⁻¹ * l * g ∈ K := by sorry
