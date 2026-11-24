-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_finite_out_mem
-- name    : GlobalTheory.CompanionTheory.HeckeMul.finite_out_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:22.283264+00:00
-- url     : https://prove2.me/theorems/d5ba2f34-6d3b-4391-a0d4-604d70db1ad7
-- title:
--   Hecke Mul: finite out mem
-- statement:
--   The Hecke Mul construction uses the finite out mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L33-L40

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
variable {G : Type} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.CompanionTheory.HeckeMul.finite_out_mem (K : Subgroup G) (hK : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    {q : G ⧸ K | q.out ∈ C}.Finite := by sorry
