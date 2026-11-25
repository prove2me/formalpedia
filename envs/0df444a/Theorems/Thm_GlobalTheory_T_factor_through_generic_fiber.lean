-- Prove2me | Theorems.Thm_GlobalTheory_T_factor_through_generic_fiber
-- name    : GlobalTheory.T.factor_through_generic_fiber
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:52.426911+00:00
-- url     : https://prove2.me/theorems/ec65349d-6502-44a6-98f2-295525bc8d95
-- title:
--   T: factor through generic fiber
-- statement:
--   The T construction uses the factor through generic fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FactorThroughGenericFiberStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FactorThroughGenericFiberStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FactorThroughGenericFiber
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FactorThroughGenericFiberStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.factor_through_generic_fiber : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0}) (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) → ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by sorry
