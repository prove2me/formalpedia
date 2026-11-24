-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_closed_restrict_of_dense
-- name    : GlobalTheory.DenseClosedAffineSubsets.closed_restrict_of_dense
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:39.275812+00:00
-- url     : https://prove2.me/theorems/03e348b4-0e6d-418f-a938-6bf7836ac1b8
-- title:
--   Dense Closed Affine Subsets: closed restrict of dense
-- statement:
--   The Dense Closed Affine Subsets construction uses the closed restrict of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L34-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L34-L57

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

theorem GlobalTheory.DenseClosedAffineSubsets.closed_restrict_of_dense {V X T P Y : Scheme.{0}} (p : T ⟶ P) [IsSeparated p] (ι : X ⟶ T)
    [IsClosedImmersion ι] (j : V ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (D : P.Opens) (y : Y ⟶ D) [IsClosedImmersion y] (e : Y ⟶ T) (he : e ≫ p = y ≫ D.ι)
    (hv : ∀ (Z : Scheme.{0}) (a : Z ⟶ V) (b : Z ⟶ D), a ≫ j ≫ ι ≫ p = b ≫ D.ι →
      ∃ v : Z ⟶ Y, v ≫ e = a ≫ j ≫ ι) :
    IsClosedImmersion ((ι ≫ p) ∣_ D) := by sorry
