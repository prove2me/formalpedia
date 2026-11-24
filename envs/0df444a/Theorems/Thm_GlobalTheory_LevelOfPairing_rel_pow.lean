-- Prove2me | Theorems.Thm_GlobalTheory_LevelOfPairing_rel_pow
-- name    : GlobalTheory.LevelOfPairing.rel_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:02:46.874097+00:00
-- url     : https://prove2.me/theorems/53686aea-3ab6-42d8-af68-4983ba01179d
-- title:
--   Level Of Pairing: rel pow
-- statement:
--   The Level Of Pairing construction uses the rel pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L36-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LevelOfPairing
variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}

theorem GlobalTheory.LevelOfPairing.rel_pow (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {x y : G} {c : U}
    (h₁ : R 1 y 1) (h : R x y c) (a : ℕ) : R (x ^ a) y (c ^ a) := by sorry
