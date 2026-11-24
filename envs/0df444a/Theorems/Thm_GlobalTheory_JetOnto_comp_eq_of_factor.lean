-- Prove2me | Theorems.Thm_GlobalTheory_JetOnto_comp_eq_of_factor
-- name    : GlobalTheory.JetOnto.comp_eq_of_factor
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:14.857689+00:00
-- url     : https://prove2.me/theorems/6710b592-301a-4428-b241-e4b590b131bb
-- title:
--   Jet Onto: comp eq of factor
-- statement:
--   The Jet Onto construction uses the comp eq of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetChartCoordinatesNilpotent.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetChartCoordinatesNilpotent.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetOnto
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem GlobalTheory.JetOnto.comp_eq_of_factor {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] {X : Over (Spec (CommRingCat.of R))} (p : A →ₐ[R] B) (q : B →ₐ[R] C)
    {y y' : sp (R₀ := R) A ⟶ X} (h : spMap p ≫ y = spMap p ≫ y') :
    spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := by sorry
