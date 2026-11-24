-- Prove2me | Theorems.Thm_GlobalTheory_exists_isAffineOpen_le_of_isQProjOver
-- name    : GlobalTheory.exists_isAffineOpen_le_of_isQProjOver
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:22.820744+00:00
-- url     : https://prove2.me/theorems/c8fb4e4c-d48d-4b41-8764-ee1f2b79f7e6
-- title:
--   Global Theory: exists is Affine Open le of is QProj Over
-- statement:
--   The Global Theory construction uses the exists is Affine Open le of is QProj Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsAffineOpenLeOfIsQProjOver.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsAffineOpenLeOfIsQProjOver.lean#L10-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsAffineOpenLeOfIsQProjOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.exists_isAffineOpen_le_of_isQProjOver :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      ∀ (F : Set X) (U : X.Opens), F.Finite → F ⊆ U →
        ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ V ∧ V ≤ U := by sorry
