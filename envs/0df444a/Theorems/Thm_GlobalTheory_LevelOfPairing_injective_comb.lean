-- Prove2me | Theorems.Thm_GlobalTheory_LevelOfPairing_injective_comb
-- name    : GlobalTheory.LevelOfPairing.injective_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:58.441764+00:00
-- url     : https://prove2.me/theorems/33ef1c5a-81a2-451d-b6c7-439d2dff7439
-- title:
--   Level Of Pairing: injective comb
-- statement:
--   The Level Of Pairing construction uses the injective comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L67-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L67-L89

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

theorem GlobalTheory.LevelOfPairing.injective_comb (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {ζ : U} (hζ : IsPrimitiveRoot ζ M)
    {g : ℕ} (y : Fin (2 * g) → G) (hy : ∀ i, y i ^ M = 1) (hp : ∀ i j, R (y i) (y j) (ζ ^ stdSymp g i j))
    (c c' : Fin (2 * g) → Fin M)
    (e : (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod) : c = c' := by sorry
