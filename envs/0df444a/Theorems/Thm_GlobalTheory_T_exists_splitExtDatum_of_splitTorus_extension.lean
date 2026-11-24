-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_splitExtDatum_of_splitTorus_extension
-- name    : GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:19.832808+00:00
-- url     : https://prove2.me/theorems/7d963227-1e1b-4f81-a5d3-2c39f693f246
-- title:
--   T: exists split Ext Datum of split Torus extension
-- statement:
--   The T construction uses the exists split Ext Datum of split Torus extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtensionStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtensionStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtensionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B], IsAbelianScheme B → ∀ (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∃ (O : X → RigLB B) (h₁ : _) (h₂ : _) (h₃ : _), ∀ hB : IsAbelianScheme B, ∃ d : (SplitExt.mk B hB X O h₁ h₂ h₃).GtDatum G, d.q = q ∧ d.i = i := by sorry
