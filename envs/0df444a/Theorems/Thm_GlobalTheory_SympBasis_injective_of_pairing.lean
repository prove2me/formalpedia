-- Prove2me | Theorems.Thm_GlobalTheory_SympBasis_injective_of_pairing
-- name    : GlobalTheory.SympBasis.injective_of_pairing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:25:16.346944+00:00
-- url     : https://prove2.me/theorems/1607b895-ef2c-429c-98ab-44d433e0d9ab
-- title:
--   Symp Basis: injective of pairing
-- statement:
--   The Symp Basis construction uses the injective of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymplecticTorsionSystemIsGeometricBasis.lean#L79-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymplecticTorsionSystemIsGeometricBasis.lean#L79-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
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
open GlobalTheory GlobalTheory.SympBasis

theorem GlobalTheory.SympBasis.injective_of_pairing {M U : Type} [CommMonoid M] [CommGroup U] (W : M → M → U → Prop) (k : ℕ) [NeZero k]
    (hu : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) {g : ℕ} (p : Fin (2 * g) → M)
    (hp : ∀ i, p i ^ k = 1) (z : U) (hz : IsPrimitiveRoot z k)
    (hw : ∀ i j, W (p i) (p j) (z ^ Out.stdSymp g i j)) :
    Function.Injective fun c : Fin (2 * g) → ZMod k => ∏ i, p i ^ (c i).val := by sorry
