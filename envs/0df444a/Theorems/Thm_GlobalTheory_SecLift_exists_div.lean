-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_exists_div
-- name    : GlobalTheory.SecLift.exists_div
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:29.038969+00:00
-- url     : https://prove2.me/theorems/9e288664-c23a-4871-baef-17fe173c1414
-- title:
--   Sec Lift: exists div
-- statement:
--   The Sec Lift construction uses the exists div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L111-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L111-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]

theorem GlobalTheory.SecLift.exists_div {f : X ⟶ Spec (CommRingCat.of A)} {j : Y ⟶ X} {a : A}
    (hS : ∀ (y : Y) (e : X.presheaf.stalk (j y)),
      cstS (𝟙 X ≫ f) (j y) a * e = 0 → (j.stalkMap y).hom e = 0)
    (W : X.Opens) (d : Γ(X, W))
    (hd : ∀ (V : X.Opens) (hle : V ≤ W), IsAffineOpen V → ∃ e, rs X hle d = cst f V a * e) :
    ∃ φ : Γ(Y, j ⁻¹ᵁ W), ∀ (y : Y) (h : j y ∈ W), ∃ e, gr (𝟙 X) (j y) W h d =
      cstS (𝟙 X ≫ f) (j y) a * e ∧ (j.stalkMap y).hom e = gr (𝟙 Y) y (j ⁻¹ᵁ W) h φ := by sorry
