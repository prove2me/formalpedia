-- Prove2me | Theorems.Thm_GlobalTheory_ZM_levelFactor_bij
-- name    : GlobalTheory.ZM.levelFactor_bij
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:41.670322+00:00
-- url     : https://prove2.me/theorems/dce34ef3-3b17-49d9-b393-f3b061a44d4e
-- title:
--   ZM: level Factor bij
-- statement:
--   The ZM construction uses the level Factor bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelOnFactorOfEighthPowerAbelianScheme.lean#L47-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelOnFactorOfEighthPowerAbelianScheme.lean#L47-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelOnFactorOfEighthPowerAbelianScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM

theorem GlobalTheory.ZM.levelFactor_bij {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (hk : 0 < k) (ht : ∀ i, P i ^ k = 1)
    (hπ : ∀ y : Fin m → H, ∃! x : G, ∀ u, π u x = y u)
    (hb : ∀ y : G, y ^ k = 1 → ∃! c : Fin n → ZMod k, (List.ofFn fun i => P i ^ (c i).val).prod = y) :
    (∀ x, L x = 1 ↔ ∃ y, x = k • y) ∧ ∀ y : H, y ^ k = 1 → ∃ x, L x = y := by sorry
