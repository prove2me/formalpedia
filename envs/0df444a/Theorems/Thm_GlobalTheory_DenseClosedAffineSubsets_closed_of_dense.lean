-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_closed_of_dense
-- name    : GlobalTheory.DenseClosedAffineSubsets.closed_of_dense
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:53.318134+00:00
-- url     : https://prove2.me/theorems/aa58a93c-0e4f-4f1d-a2e3-1c0a978f8bcb
-- title:
--   Dense Closed Affine Subsets: closed of dense
-- statement:
--   The Dense Closed Affine Subsets construction uses the closed of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L13-L28

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

theorem GlobalTheory.DenseClosedAffineSubsets.closed_of_dense {V X T D Y : Scheme.{0}} (p : T ⟶ D) [IsSeparated p] (ι : X ⟶ T)
    [IsClosedImmersion ι] (j : V ⟶ X) [IsSchemeTheoreticallyDominant j] (e : Y ⟶ T)
    [IsClosedImmersion (e ≫ p)] (v : V ⟶ Y) (hv : v ≫ e = j ≫ ι) :
    IsClosedImmersion (ι ≫ p) := by sorry
