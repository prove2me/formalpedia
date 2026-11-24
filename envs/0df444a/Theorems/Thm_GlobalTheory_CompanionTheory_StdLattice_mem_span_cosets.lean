-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_mem_span_cosets
-- name    : GlobalTheory.CompanionTheory.StdLattice.mem_span_cosets
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:30.898347+00:00
-- url     : https://prove2.me/theorems/3181312b-0418-4c99-a27d-a64ad7e0f5da
-- title:
--   Std Lattice: mem span cosets
-- statement:
--   The Std Lattice construction uses the mem span cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L22-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean#L22-L63

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

theorem GlobalTheory.CompanionTheory.StdLattice.mem_span_cosets {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {f : G → ℂ}
    (hf : HasCompactSupport f) (H : AddSubgroup G) (hH : IsOpen (H : Set G))
    (hinv : ∀ y ∈ tsupport f, ∀ u ∈ H, f (y + u) = f y) :
    f ∈ Submodule.span ℂ (Set.range fun a : G => fun x : G => (H : Set G).indicator (fun _ => (1 : ℂ)) (x + a)) := by sorry
