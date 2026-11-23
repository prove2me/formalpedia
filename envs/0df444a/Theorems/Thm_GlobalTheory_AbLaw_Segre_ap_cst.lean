-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_cst
-- name    : GlobalTheory.AbLaw.Segre.ap_cst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:25.307776+00:00
-- url     : https://prove2.me/theorems/1ba9414e-d514-4b90-8bf9-b2eb4843c51b
-- title:
--   Segre: ap cst
-- statement:
--   The Segre construction uses the ap cst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L28-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]

theorem GlobalTheory.AbLaw.Segre.ap_cst (p : P ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {W : P.Opens}
    (h : W ≤ p ⁻¹ᵁ U) (r : R) : ap p h (cst f U r) = cst (p ≫ f) W r := by sorry
