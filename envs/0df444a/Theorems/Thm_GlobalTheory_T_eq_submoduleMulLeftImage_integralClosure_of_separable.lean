-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_submoduleMulLeftImage_integralClosure_of_separable
-- name    : GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:25.161872+00:00
-- url     : https://prove2.me/theorems/9c50679e-effc-44e4-98b4-c743748cbc0e
-- title:
--   T: eq submodule Mul Left Image integral Closure of separable
-- statement:
--   The T construction uses the eq submodule Mul Left Image integral Closure of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement
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

theorem GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N → (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) → ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by sorry
