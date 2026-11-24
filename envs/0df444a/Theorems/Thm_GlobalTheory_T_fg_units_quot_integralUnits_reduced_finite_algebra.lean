-- Prove2me | Theorems.Thm_GlobalTheory_T_fg_units_quot_integralUnits_reduced_finite_algebra
-- name    : GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:39:58.673422+00:00
-- url     : https://prove2.me/theorems/fbd852e2-9e81-4b4a-a4a9-eb8912a78270
-- title:
--   T: fg units quot integral Units reduced finite algebra
-- statement:
--   The T construction uses the fg units quot integral Units reduced finite algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
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

theorem GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) → ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A] [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by sorry
