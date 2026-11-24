-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_mem_span_schr
-- name    : GlobalTheory.CompanionTheory.StdLattice.mem_span_schr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:44.125517+00:00
-- url     : https://prove2.me/theorems/ca52e2d5-5f21-4a7c-b277-d88b9c1cdd2c
-- title:
--   Std Lattice: mem span schr
-- statement:
--   The Std Lattice construction uses the mem span schr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L111-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L111-L158

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StdLattice
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [TopologicalSpace R]
variable [IsTopologicalRing R] [Invertible (2 : R)]

theorem GlobalTheory.CompanionTheory.StdLattice.mem_span_schr [LocallyCompactSpace R] [T2Space R] {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ}
    (h : GoodChar ψ O u) {f : (κ → R) → ℂ} (hf : f ∈ SB (κ → R)) :
    f ∈ Submodule.span ℂ (Set.range fun w => schr ψ w (ind O κ)) := by sorry
