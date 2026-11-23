-- Prove2me | Theorems.Thm_GlobalTheory_LevelOfPairing_surjective_comb
-- name    : GlobalTheory.LevelOfPairing.surjective_comb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:38.938404+00:00
-- url     : https://prove2.me/theorems/4917326d-6e85-4e01-b928-51a274f813f1
-- title:
--   Level Of Pairing: surjective comb
-- statement:
--   The Level Of Pairing construction uses the surjective comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L91-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L91-L102

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

theorem GlobalTheory.LevelOfPairing.surjective_comb (cm : ∀ a b : G, Commute a b) (hM : M ≠ 0) {n : ℕ} (y : Fin n → G)
    (hy : ∀ i, y i ^ M = 1) (hcard : Nat.card {x : G // x ^ M = 1} = M ^ n)
    (hinj : ∀ c c' : Fin n → Fin M,
      (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod → c = c')
    (z : G) (hz : z ^ M = 1) : ∃ c : Fin n → Fin M, (List.ofFn fun i => y i ^ (c i : ℕ)).prod = z := by sorry
