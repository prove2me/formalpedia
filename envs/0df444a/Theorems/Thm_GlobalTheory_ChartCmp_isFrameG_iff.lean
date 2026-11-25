-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_isFrameG_iff
-- name    : GlobalTheory.ChartCmp.isFrameG_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:30.727934+00:00
-- url     : https://prove2.me/theorems/29f5987a-eeb3-54e2-a024-9cabe6c6d440
-- title:
--   Chart Cmp: is Frame G iff
-- statement:
--   The Chart Cmp construction uses the is Frame G iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/AdditionLawSecondIdentity.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/AdditionLawSecondIdentity.lean#L137-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartCmp
open MvPolynomial (X C)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem GlobalTheory.ChartCmp.isFrameG_iff (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) :
    IsFrameG t x0 d x F act ph1 ph2 sy ad e ↔ (∀ m, (e m).IsGen) ∧ FamPh1 t x0 d x F ph1 e ∧ FamPh2 t x0 d x F ph2 e ∧
      FamSy t x0 d x sy e ∧ FamAd t x0 d x act ad e := by sorry
