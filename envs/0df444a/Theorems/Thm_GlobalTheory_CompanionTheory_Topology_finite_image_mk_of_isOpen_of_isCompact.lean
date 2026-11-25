-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Topology_finite_image_mk_of_isOpen_of_isCompact
-- name    : GlobalTheory.CompanionTheory.Topology.finite_image_mk_of_isOpen_of_isCompact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:47.408093+00:00
-- url     : https://prove2.me/theorems/b19b81fe-99bc-5bf8-813e-5aadba7c3455
-- title:
--   Topology: finite image mk of is Open of is Compact
-- statement:
--   The Topology construction uses the finite image mk of is Open of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteImageCompactOpenQuotient.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteImageCompactOpenQuotient.lean#L8-L21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactOpenQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Topology

theorem GlobalTheory.CompanionTheory.Topology.finite_image_mk_of_isOpen_of_isCompact :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      (H : AddSubgroup G) (K : Set G), IsOpen (H : Set G) → IsCompact K →
      (QuotientAddGroup.mk '' K : Set (G ⧸ H)).Finite := by sorry
