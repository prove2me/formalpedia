-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_termPull
-- name    : GlobalTheory.FieldBaseChange.isExtension_termPull
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:11.669275+00:00
-- url     : https://prove2.me/theorems/a56896f2-d67d-41f3-97f1-87e07b4e305c
-- title:
--   Field Base Change: is Extension term Pull
-- statement:
--   The Field Base Change construction uses the is Extension term Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsFinsetRepresentatives.lean#L179-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsFinsetRepresentatives.lean#L179-L180

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (E F : Type) [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]

theorem GlobalTheory.FieldBaseChange.isExtension_termPull (k : ℕ) (α : D.X) : IsExtension (termPull D E F k α) := by sorry
