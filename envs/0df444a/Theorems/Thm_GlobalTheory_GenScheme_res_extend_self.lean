-- Prove2me | Theorems.Thm_GlobalTheory_GenScheme_res_extend_self
-- name    : GlobalTheory.GenScheme.res_extend_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:18:46.206482+00:00
-- url     : https://prove2.me/theorems/30853cdb-62a1-4f41-9b4d-bac5b6e015ca
-- title:
--   Gen Scheme: res extend self
-- statement:
--   The Gen Scheme construction uses the res extend self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L82-L86

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
variable {B Z : Scheme.{0}} (L : LB B) (b : Z ⟶ B)
variable (j : L.ι) (hj : ⊤ ≤ b ⁻¹ᵁ L.U j)
variable {L}

theorem GlobalTheory.GenScheme.res_extend_self (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : res hj (extend L b j hj t j) = t := by sorry
