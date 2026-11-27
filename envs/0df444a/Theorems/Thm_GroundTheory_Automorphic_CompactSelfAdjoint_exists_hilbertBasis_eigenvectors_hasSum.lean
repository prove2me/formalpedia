-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_exists_hilbertBasis_eigenvectors_hasSum
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:52.810837+00:00
-- url     : https://prove2.me/theorems/9f6fb033-e7fb-56ca-bedb-95170ac5b59c
-- title:
--   Compact Self Adjoint: exists hilbert Basis eigenvectors has Sum
-- statement:
--   The Compact Self Adjoint construction uses the exists hilbert Basis eigenvectors has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L217-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L217-L243

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (l : s → ℝ), ⇑b = ((↑) : s → E) ∧
      (∀ i, T (b i) = (l i : 𝕜) • b i) ∧
      (∀ x, HasSum (fun i => ((l i : 𝕜) * ⟪b i, x⟫) • b i) (T x)) ∧
      ∀ ε > 0, {i | ε ≤ |l i|}.Finite := by sorry
