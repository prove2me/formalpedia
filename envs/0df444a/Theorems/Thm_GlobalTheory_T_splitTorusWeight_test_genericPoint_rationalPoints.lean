-- Prove2me | Theorems.Thm_GlobalTheory_T_splitTorusWeight_test_genericPoint_rationalPoints
-- name    : GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:17:48.795909+00:00
-- url     : https://prove2.me/theorems/251cd1bb-48df-4d28-bbf4-7b460180f029
-- title:
--   T: split Torus Weight test generic Point rational Points
-- statement:
--   The T construction uses the split Torus Weight test generic Point rational Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusWeightTestGenericPointRationalPointsStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusWeightTestGenericPointRationalPointsStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPointsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by sorry
