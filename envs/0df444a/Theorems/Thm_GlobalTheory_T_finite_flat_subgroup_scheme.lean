-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_flat_subgroup_scheme
-- name    : GlobalTheory.T.finite_flat_subgroup_scheme
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:54.92886+00:00
-- url     : https://prove2.me/theorems/715fa302-f036-44fd-ba52-733846e21865
-- title:
--   T: finite flat subgroup scheme
-- statement:
--   The T construction uses the finite flat subgroup scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupSchemeStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupSchemeStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupSchemeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_flat_subgroup_scheme : ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by sorry
