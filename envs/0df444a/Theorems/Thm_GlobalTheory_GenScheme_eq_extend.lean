-- Prove2me | Theorems.Thm_GlobalTheory_GenScheme_eq_extend
-- name    : GlobalTheory.GenScheme.eq_extend
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:26.4159+00:00
-- url     : https://prove2.me/theorems/0e666bbf-5627-400a-8299-1a143329ea1f
-- title:
--   Gen Scheme: eq extend
-- statement:
--   The Gen Scheme construction uses the eq extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L88-L93

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

theorem GlobalTheory.GenScheme.eq_extend {s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ} (hs : Compat L b s) (i : L.ι) :
    s i = extend L b j hj (res hj (s j)) i := by sorry
