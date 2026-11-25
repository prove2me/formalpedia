-- Prove2me | Theorems.Thm_GlobalTheory_T_surjective_pullHO2_of_pullHO1
-- name    : GlobalTheory.T.surjective_pullHO2_of_pullHO1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:25.49394+00:00
-- url     : https://prove2.me/theorems/d9c0730a-56e4-573a-b1cd-12cc5dc4c38f
-- title:
--   T: surjective pull HO2 of pull HO1
-- statement:
--   The T construction uses the surjective pull HO2 of pull HO1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectivePullHO2OfPullHO1Statement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectivePullHO2OfPullHO1Statement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectivePullHO2OfPullHO1
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectivePullHO2OfPullHO1Statement
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
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.surjective_pullHO2_of_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by sorry
