-- Prove2me | Theorems.Thm_GlobalTheory_SqZero_away_ext
-- name    : GlobalTheory.SqZero.away_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.080877+00:00
-- url     : https://prove2.me/theorems/e97ad63d-e2ee-47ab-ad19-502715c0c647
-- title:
--   Sq Zero: away ext
-- statement:
--   The Sq Zero construction uses the away ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SpanEqTopOfForallMaximal.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SpanEqTopOfForallMaximal.lean#L202-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {X : Over (Spec (CommRingCat.of R))} {A : Type} [CommRing A] [Algebra R A]
  {κ : Type} {s : κ → A} {B : κ → Type} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

theorem GlobalTheory.SqZero.away_ext (hs : Ideal.span (Set.range s) = ⊤) (q : ∀ i, A →ₐ[R] B i)
    (hq : ∀ i, IsAway (q i) (s i)) {y y' : sp A ⟶ X}
    (h : ∀ i, spMap (q i) ≫ y = spMap (q i) ≫ y') : y = y' := by sorry
