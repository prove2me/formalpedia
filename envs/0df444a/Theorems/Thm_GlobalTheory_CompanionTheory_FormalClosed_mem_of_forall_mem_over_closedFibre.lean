-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FormalClosed_mem_of_forall_mem_over_closedFibre
-- name    : GlobalTheory.CompanionTheory.FormalClosed.mem_of_forall_mem_over_closedFibre
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:52:36.612603+00:00
-- url     : https://prove2.me/theorems/13ce3cf0-33a8-599d-b4e4-d45c981287d3
-- title:
--   Formal Closed: mem of forall mem over closed Fibre
-- statement:
--   The Formal Closed construction uses the mem of forall mem over closed Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsIsoOfIsClosedImmersionOfThickenings.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsIsoOfIsClosedImmersionOfThickenings.lean#L12-L32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsIsoOfIsClosedImmersionOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FormalClosed
open GlobalTheory.ThickeningClosed

theorem GlobalTheory.CompanionTheory.FormalClosed.mem_of_forall_mem_over_closedFibre {R : Type} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {W : Set X} (hW : IsOpen W)
    (h : ∀ x, I ≤ (f x).asIdeal → x ∈ W) (x : X) : x ∈ W := by sorry
