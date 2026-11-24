-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_exists_hilbertBasis_subset_iUnion
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_subset_iUnion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:40.949974+00:00
-- url     : https://prove2.me/theorems/21cfc14e-e6d2-4d25-b57b-c1b8e4f60b8f
-- title:
--   Compact Self Adjoint: exists hilbert Basis subset i Union
-- statement:
--   The Compact Self Adjoint construction uses the exists hilbert Basis subset i Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L34-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L34-L70

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.CompactSelfAdjoint
open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable [CompleteSpace E]

theorem GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_subset_iUnion {α : Type*} (W : α → Submodule 𝕜 E)
    (hW : OrthogonalFamily 𝕜 (fun a => W a) fun a => (W a).subtypeₗᵢ)
    (hc : ∀ a, IsClosed (W a : Set E)) (hbot : (⨆ a, W a)ᗮ = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧ s ⊆ ⋃ a, (W a : Set E) := by sorry
