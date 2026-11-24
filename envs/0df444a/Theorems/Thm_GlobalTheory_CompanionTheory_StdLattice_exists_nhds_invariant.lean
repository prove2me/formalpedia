-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_exists_nhds_invariant
-- name    : GlobalTheory.CompanionTheory.StdLattice.exists_nhds_invariant
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:25.366498+00:00
-- url     : https://prove2.me/theorems/1067c98c-3a1f-4751-b6d7-6b701d238f52
-- title:
--   Std Lattice: exists nhds invariant
-- statement:
--   The Std Lattice construction uses the exists nhds invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L11-L20

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

theorem GlobalTheory.CompanionTheory.StdLattice.exists_nhds_invariant {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {f : G → ℂ}
    (hf : f ∈ SB G) : ∀ᶠ u in 𝓝 (0 : G), ∀ y ∈ tsupport f, f (y + u) = f y := by sorry
