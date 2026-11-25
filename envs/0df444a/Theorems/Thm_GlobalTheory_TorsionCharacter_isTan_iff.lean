-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCharacter_isTan_iff
-- name    : GlobalTheory.TorsionCharacter.isTan_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:43:32.250865+00:00
-- url     : https://prove2.me/theorems/9514d5af-d1af-5b72-a6f5-e9cf06c3d069
-- title:
--   Torsion Character: is Tan iff
-- statement:
--   The Torsion Character construction uses the is Tan iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLieCoordinates.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLieCoordinates.lean#L50-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (Pt comp1)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {O : Type} [CommRing O] {Gt G' : Over (Spec (CommRingCat.of O))} [GrpObj Gt] [GrpObj G']
  (K : (specO O (DualNumber O) ⟶ Gt) → (specO O (DualNumber O) ⟶ G'))
  (hmul : ∀ w w', K (w * w') = K w * K w') (hinj : Function.Injective K)
  (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w)
include hmul hinj hnat

theorem GlobalTheory.TorsionCharacter.isTan_iff (w : specO O (DualNumber O) ⟶ Gt) : IsTan w ↔ IsTan (K w) := by sorry
