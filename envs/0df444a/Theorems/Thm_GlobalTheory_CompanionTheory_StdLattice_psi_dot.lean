-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_psi_dot
-- name    : GlobalTheory.CompanionTheory.StdLattice.psi_dot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:35.149852+00:00
-- url     : https://prove2.me/theorems/defd4390-66ea-42d1-a539-f73982bb0bde
-- title:
--   Std Lattice: psi dot
-- statement:
--   The Std Lattice construction uses the psi dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L98-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L98-L107

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

theorem GlobalTheory.CompanionTheory.StdLattice.psi_dot {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) {x y : κ → R} (hx : ∀ i, x i ∈ O)
    (hy : y ∈ box O u κ) : ψ (x ⬝ᵥ y) = 1 := by sorry
