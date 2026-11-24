-- Prove2me | Theorems.Thm_GlobalTheory_LevelOfPairing_rel_prod
-- name    : GlobalTheory.LevelOfPairing.rel_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:21.776801+00:00
-- url     : https://prove2.me/theorems/e9f87b50-8a23-43b1-b528-318220e33270
-- title:
--   Level Of Pairing: rel prod
-- statement:
--   The Level Of Pairing construction uses the rel prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L42-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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

theorem GlobalTheory.LevelOfPairing.rel_prod (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {y : G}
    (h₁ : R 1 y 1) : ∀ {n : ℕ} (x : Fin n → G) (c : Fin n → U), (∀ i, R (x i) y (c i)) →
      R (List.ofFn x).prod y (∏ i, c i)
  := by sorry
