-- Prove2me | Theorems.Thm_GlobalTheory_LevelOfPairing_prod_pow_eq_one
-- name    : GlobalTheory.LevelOfPairing.prod_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:37.849357+00:00
-- url     : https://prove2.me/theorems/89dfe72e-2356-4203-b3a2-ec1958eeaa94
-- title:
--   Level Of Pairing: prod pow eq one
-- statement:
--   The Level Of Pairing construction uses the prod pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L19-L24

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

theorem GlobalTheory.LevelOfPairing.prod_pow_eq_one (cm : ∀ a b : G, Commute a b) {n : ℕ} (y : Fin n → G) (hy : ∀ i, y i ^ M = 1)
    (a : Fin n → ℕ) : (List.ofFn fun i => y i ^ a i).prod ^ M = 1 := by sorry
