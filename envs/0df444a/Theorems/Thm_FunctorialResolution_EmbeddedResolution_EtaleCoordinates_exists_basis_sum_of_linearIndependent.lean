-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_basis_sum_of_linearIndependent
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_basis_sum_of_linearIndependent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:17.572411+00:00
-- url     : https://prove2.me/theorems/3f02aee7-fea6-4bc0-9e61-7c6d8c0eb65a
-- title:
--   Etale Coordinates: exists basis sum of linear Independent
-- statement:
--   The Etale Coordinates construction uses the exists basis sum of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/FormallyEtaleCoordinates.lean#L50-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/FormallyEtaleCoordinates.lean#L50-L138

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_basis_sum_of_linearIndependent {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (h : ℕ)
    (c : Fin h → V) (hc : LinearIndependent K c) :
    ∃ (J : Finset ι) (B : Module.Basis (Fin h ⊕ {j : ι // j ∈ J}) K V),
      (∀ i : Fin h, B (Sum.inl i) = c i) ∧
        ∀ j : {j : ι // j ∈ J}, B (Sum.inr j) = b (j : ι) := by sorry
