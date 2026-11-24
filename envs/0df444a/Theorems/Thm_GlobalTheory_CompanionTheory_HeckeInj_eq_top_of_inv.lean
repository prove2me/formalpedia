-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_eq_top_of_inv
-- name    : GlobalTheory.CompanionTheory.HeckeInj.eq_top_of_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:53.264069+00:00
-- url     : https://prove2.me/theorems/ff955250-80b5-4e4f-84a6-17a7bce79fec
-- title:
--   Hecke Inj: eq top of inv
-- statement:
--   The Hecke Inj construction uses the eq top of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L19-L28

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

theorem GlobalTheory.CompanionTheory.HeckeInj.eq_top_of_inv {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (N : Submodule ℂ V) (hN : ∀ g, ∀ v ∈ N, ρ g v ∈ N) {w : V} (hw : w ∈ N)
    (h0 : w ≠ 0) : N = ⊤ := by sorry
