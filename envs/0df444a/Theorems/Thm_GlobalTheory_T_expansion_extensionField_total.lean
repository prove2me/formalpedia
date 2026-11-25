-- Prove2me | Theorems.Thm_GlobalTheory_T_expansion_extensionField_total
-- name    : GlobalTheory.T.expansion_extensionField_total
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:45:10.276212+00:00
-- url     : https://prove2.me/theorems/57ecdc2c-01d3-5c0e-9d4d-147ebeac70e2
-- title:
--   T: expansion extension Field total
-- statement:
--   The T construction uses the expansion extension Field total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpansionExtensionFieldTotalStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpansionExtensionFieldTotalStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpansionExtensionFieldTotal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpansionExtensionFieldTotalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.expansion_extensionField_total : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → (∀ s : Fam D.toPre F k, ∃ t, U.toUnifPre.ExpandsF F k w t s) ∧ ∀ t, ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by sorry
