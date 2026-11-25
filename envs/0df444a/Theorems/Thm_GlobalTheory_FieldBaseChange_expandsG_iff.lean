-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_expandsG_iff
-- name    : GlobalTheory.FieldBaseChange.expandsG_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:47:50.003817+00:00
-- url     : https://prove2.me/theorems/4ef8d5bc-d6bc-48fa-96c7-5ae1ec9df43d
-- title:
--   Field Base Change: expands G iff
-- statement:
--   The Field Base Change construction uses the expands G iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L246-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L246-L266

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

theorem GlobalTheory.FieldBaseChange.expandsG_iff (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) :
    U.ExpandsG F k v s ↔ ∃ (n : ℕ) (c : Fin n → F) (x : Fin n → IntSec U k × ∀ α, IntTerm D k α),
      (∀ i, x i ∈ expansionPairs U k) ∧ v = ∑ i, c i • extendSec U F k (genericSec U k (x i).1) ∧
      ∀ α, famProj D.toPre F k α s =
        ∑ i, c i • termPull D.toPre (FractionRing R) F k α (genericTerm D k α ((x i).2 α)) := by sorry
