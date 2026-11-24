-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_exists_closed_affineSpace
-- name    : GlobalTheory.DenseClosedAffineSubsets.exists_closed_affineSpace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:30.081986+00:00
-- url     : https://prove2.me/theorems/e230589d-6e0e-4518-b4ed-e14a25b9d844
-- title:
--   Dense Closed Affine Subsets: exists closed affine Space
-- statement:
--   The Dense Closed Affine Subsets construction uses the exists closed affine Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L59-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L59-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets

theorem GlobalTheory.DenseClosedAffineSubsets.exists_closed_affineSpace {U S : Scheme.{0}} [IsAffine U] [IsAffine S] (u : U ⟶ S)
    [LocallyOfFiniteType u] :
    ∃ (σ : Type) (_ : Fintype σ) (g : σ → Γ(U, ⊤)),
      IsClosedImmersion (AffineSpace.homOfVector u g) := by sorry
