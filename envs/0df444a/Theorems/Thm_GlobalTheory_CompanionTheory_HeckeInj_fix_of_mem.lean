-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_fix_of_mem
-- name    : GlobalTheory.CompanionTheory.HeckeInj.fix_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:02.569177+00:00
-- url     : https://prove2.me/theorems/2ff36ff0-26ff-492e-b4b9-00a5da5b642c
-- title:
--   Hecke Inj: fix of mem
-- statement:
--   The Hecke Inj construction uses the fix of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L14-L17

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
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.HeckeInj.fix_of_mem {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
    {v : V} (hv : v ∈ fixed ρ K) {c : G} (hc : c ∈ K) : ρ c v = v := by sorry
