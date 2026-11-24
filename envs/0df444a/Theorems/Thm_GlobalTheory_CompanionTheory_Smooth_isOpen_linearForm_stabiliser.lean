-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Smooth_isOpen_linearForm_stabiliser
-- name    : GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:28.998068+00:00
-- url     : https://prove2.me/theorems/7c133b9b-e6aa-4cd2-844d-ee036e78fc6f
-- title:
--   Smooth: is Open linear Form stabiliser
-- statement:
--   The Smooth construction uses the is Open linear Form stabiliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalOpenStabilizer.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalOpenStabilizer.lean#L26-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalOpenStabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Smooth

theorem GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} := by sorry
