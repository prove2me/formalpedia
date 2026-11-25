-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_PrimLift_primO1_of_axesO1
-- name    : GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:32:32.798585+00:00
-- url     : https://prove2.me/theorems/a0d88f19-491f-5c36-bfd5-d5c9ab3c85b1
-- title:
--   Prim Lift: prim O1 of axes O1
-- statement:
--   The Prim Lift construction uses the prim O1 of axes O1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveOfAxesVanishing.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveOfAxesVanishing.lean#L30-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveOfAxesVanishing
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
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.PrimLift

theorem GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by sorry
