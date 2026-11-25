-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_AddExt_exists_common_geometric_point
-- name    : GlobalTheory.ZJ.AddExt.exists_common_geometric_point
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:55.714834+00:00
-- url     : https://prove2.me/theorems/6dccaafd-8df9-5803-9cbc-cfd010ae0068
-- title:
--   Add Ext: exists common geometric point
-- statement:
--   The Add Ext construction uses the exists common geometric point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L24-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt

theorem GlobalTheory.ZJ.AddExt.exists_common_geometric_point {X S S' : Scheme.{0}} (a : S ⟶ X) (a' : S' ⟶ X) (s : S) (s' : S')
    (h : a s = a' s') : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Sp K ⟶ S) (u' : Sp K ⟶ S'),
      u ≫ a = u' ≫ a' ∧ (∀ x, u x = s) ∧ (∀ x, u' x = s') := by sorry
