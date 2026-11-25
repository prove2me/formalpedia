-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearEquiv_expandsF
-- name    : GlobalTheory.exists_linearEquiv_expandsF
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:54:27.782346+00:00
-- url     : https://prove2.me/theorems/805f4abe-3159-5a5d-a428-4a9c9c38cb87
-- title:
--   Global Theory: exists linear Equiv expands F
-- statement:
--   The Global Theory construction uses the exists linear Equiv expands F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L337-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L337-L361

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
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR FieldBaseChange

theorem GlobalTheory.exists_linearEquiv_expandsF (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) :
    ∃ e : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) ≃ₗ[F] Fam D.toPre F k,
      ∀ t s, U.toUnifPre.ExpandsF F k w t s ↔ e t = s := by sorry
