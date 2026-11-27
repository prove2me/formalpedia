-- Prove2me | Theorems.Thm_GlobalTheory_T_topologicalKrullDim_eq_of_openImmersion_integral_scheme
-- name    : GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:10.28146+00:00
-- url     : https://prove2.me/theorems/6d10e6d9-e0e2-525a-b109-f6b663f0b725
-- title:
--   T: topological Krull Dim eq of open Immersion integral scheme
-- statement:
--   The T construction uses the topological Krull Dim eq of open Immersion integral scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfOpenImmersionIntegralScheStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfOpenImmersionIntegralScheStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralScheStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme : ∀ (F : Type) [Field F] (X V : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ] [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by sorry
