-- Prove2me | Theorems.Thm_GlobalTheory_JetOnto_aug_comp_jetLift
-- name    : GlobalTheory.JetOnto.aug_comp_jetLift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:46.313195+00:00
-- url     : https://prove2.me/theorems/af93f422-f37d-4361-ab03-661bafb92e8f
-- title:
--   Jet Onto: aug comp jet Lift
-- statement:
--   The Jet Onto construction uses the aug comp jet Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetChartCoordinatesNilpotent.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetChartCoordinatesNilpotent.lean#L22-L26

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

theorem GlobalTheory.JetOnto.aug_comp_jetLift {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) {d m : ℕ}
    (h : (RingHom.ker aug) ^ (m + 1) = ⊥) (b : Fin d → A) (hb : ∀ j, b j ∈ RingHom.ker aug) :
    aug.comp (jetLift R _ h b hb) = jetAug R (Fin d) m := by sorry
