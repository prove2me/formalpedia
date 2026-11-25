-- Prove2me | Theorems.Thm_GlobalTheory_ExtSqKer_fin_two_vector_eq_matrixVecCons
-- name    : GlobalTheory.ExtSqKer.fin_two_vector_eq_matrixVecCons
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:31.189694+00:00
-- url     : https://prove2.me/theorems/cc64a61e-e916-49b4-9f49-df66ad7cadc8
-- title:
--   Ext Sq Ker: fin two vector eq matrix Vec Cons
-- statement:
--   The Ext Sq Ker construction uses the fin two vector eq matrix Vec Cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorSquareKerOfSurjective.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorSquareKerOfSurjective.lean#L57-L58

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
open GlobalTheory GlobalTheory.ExtSqKer
variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem GlobalTheory.ExtSqKer.fin_two_vector_eq_matrixVecCons (u : Fin 2 → M) : u = ![u 0, u 1] := by sorry
