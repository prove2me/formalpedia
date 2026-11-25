-- Prove2me | Theorems.Thm_GlobalTheory_T_integralClosure_fg_dvr_of_separable_charpoly
-- name    : GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:04.457991+00:00
-- url     : https://prove2.me/theorems/53c43bf7-e211-4a4c-975a-4c801466a43b
-- title:
--   T: integral Closure fg dvr of separable charpoly
-- statement:
--   The T construction uses the integral Closure fg dvr of separable charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgDvrOfSeparableCharpolyStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgDvrOfSeparableCharpolyStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpolyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by sorry
