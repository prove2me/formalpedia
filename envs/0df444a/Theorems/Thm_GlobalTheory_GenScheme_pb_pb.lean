-- Prove2me | Theorems.Thm_GlobalTheory_GenScheme_pb_pb
-- name    : GlobalTheory.GenScheme.pb_pb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:25:20.773802+00:00
-- url     : https://prove2.me/theorems/a8a5136c-8708-51f0-8e9a-c8eff3e5f9e7
-- title:
--   Gen Scheme: pb pb
-- statement:
--   The Gen Scheme construction uses the pb pb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L37-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.GenScheme.pb_pb (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    pb g V W h' (pb f U V h a) = pb (g ≫ f) U W (h'.trans (g.preimage_mono h)) a := by sorry
