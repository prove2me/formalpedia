-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_Vanish_omega_sub
-- name    : GlobalTheory.AbCoh.Vanish.omega_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:57.033922+00:00
-- url     : https://prove2.me/theorems/8384af0c-1969-45a3-8882-4340ad1c7616
-- title:
--   Vanish: omega sub
-- statement:
--   The Vanish construction uses the omega sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommAlgFunctorCohomologyTwoEqZeroOfIsInitial.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommAlgFunctorCohomologyTwoEqZeroOfIsInitial.lean#L36-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.Vanish

theorem GlobalTheory.AbCoh.Vanish.omega_sub {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s] :
    Subsingleton Ω[Sec s ⊤⁄R] := by sorry
