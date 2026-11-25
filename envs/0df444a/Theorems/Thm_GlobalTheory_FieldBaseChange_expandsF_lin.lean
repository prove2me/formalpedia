-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_expandsF_lin
-- name    : GlobalTheory.FieldBaseChange.expandsF_lin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:32.90049+00:00
-- url     : https://prove2.me/theorems/b6dcc935-1f81-57fe-bf1a-342c231c3e96
-- title:
--   Field Base Change: expands F lin
-- statement:
--   The Field Base Change construction uses the expands F lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L293-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L293-L300

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {k : ℕ} {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}

theorem GlobalTheory.FieldBaseChange.expandsF_lin (c : F) {t t' : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F))}
    {s s' : Fam D.toPre F k} (h : U.ExpandsF F k w t s) (h' : U.ExpandsF F k w t' s') :
    U.ExpandsF F k w (c • t + t' : SecOver (abelianBase A F) _) (c • s + s') := by sorry
