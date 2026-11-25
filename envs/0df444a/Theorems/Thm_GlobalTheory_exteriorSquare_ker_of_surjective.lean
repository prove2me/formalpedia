-- Prove2me | Theorems.Thm_GlobalTheory_exteriorSquare_ker_of_surjective
-- name    : GlobalTheory.exteriorSquare_ker_of_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:27.929262+00:00
-- url     : https://prove2.me/theorems/232fbe85-2dd4-5b32-a814-ce778bc41a25
-- title:
--   Global Theory: exterior Square ker of surjective
-- statement:
--   The Global Theory construction uses the exterior Square ker of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorSquareKerOfSurjective.lean#L76-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorSquareKerOfSurjective.lean#L76-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ExtSqKer

theorem GlobalTheory.exteriorSquare_ker_of_surjective (R : Type) [CommRing R] (W M H : Type)
    [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (t : ⋀[R]^2 M) (ht : exteriorPower.map 2 p t = 0) :
    ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W),
      t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by sorry
