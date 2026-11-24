-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_cosetFn_left
-- name    : GlobalTheory.CompanionTheory.HeckeInj.cosetFn_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:44.257356+00:00
-- url     : https://prove2.me/theorems/e6b334b8-ea15-426b-b824-a8f91d4e60cd
-- title:
--   Hecke Inj: coset Fn left
-- statement:
--   The Hecke Inj construction uses the coset Fn left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L68-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L68-L91

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

theorem GlobalTheory.CompanionTheory.HeckeInj.cosetFn_left (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g : G)
    (hL : ∀ l ∈ L, g⁻¹ * l * g ∈ K) (x : G) {k : G} (hk : k ∈ K) :
    cosetFn K L g (k * x) = cosetFn K L g x := by sorry
