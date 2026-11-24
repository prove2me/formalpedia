-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_cosetFn_right
-- name    : GlobalTheory.CompanionTheory.HeckeInj.cosetFn_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:50.015457+00:00
-- url     : https://prove2.me/theorems/6262d72c-fbf9-4955-86b4-d4c6e20b6fde
-- title:
--   Hecke Inj: coset Fn right
-- statement:
--   The Hecke Inj construction uses the coset Fn right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L63-L66

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

theorem GlobalTheory.CompanionTheory.HeckeInj.cosetFn_right (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g x : G) {k : G} (hk : k ∈ K) :
    cosetFn K L g (x * k) = cosetFn K L g x := by sorry
