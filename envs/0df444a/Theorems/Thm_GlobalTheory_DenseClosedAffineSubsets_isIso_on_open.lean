-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_isIso_on_open
-- name    : GlobalTheory.DenseClosedAffineSubsets.isIso_on_open
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:14.714805+00:00
-- url     : https://prove2.me/theorems/c690fe07-0f94-4bcb-bfef-18aca9b30cc9
-- title:
--   Dense Closed Affine Subsets: is Iso on open
-- statement:
--   The Dense Closed Affine Subsets construction uses the is Iso on open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L304-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L304-L322

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.DenseClosedAffineSubsets.isIso_on_open {S W P X : Scheme.{0}} (f : W ⟶ S) (s : P ⟶ S) [IsSeparated s]
    (U : W.Opens) (ι : X ⟶ pullback f s)
    [IsClosedImmersion ι] (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ ι ≫ pullback.fst f s = U.ι) :
    IsIso ((ι ≫ pullback.fst f s) ∣_ U) := by sorry
