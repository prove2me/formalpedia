-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_core
-- name    : GlobalTheory.QuadSymbol.NormIndex.core
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:50:26.041818+00:00
-- url     : https://prove2.me/theorems/758495ba-d991-4151-b72a-8a8846f8deed
-- title:
--   Norm Index: core
-- statement:
--   The Norm Index construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSquareMulInfinite.lean#L75-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSquareMulInfinite.lean#L75-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormIndex
variable {K : Type} [Field K]
variable (w : Valuation K ℤᵐ⁰)

theorem GlobalTheory.QuadSymbol.NormIndex.core (h2 : (2 : K) ≠ 0) {π Δ d : K} (hπ : w π = WithZero.exp (-1)) (hΔ : Δ ≠ 0)
    (hd : d ≠ 0) (hA : ∀ (x : K) (n : ℤ), w x = WithZero.exp (2 * n) → Nm Δ x)
    (hB : ∀ (z : K) (n : ℤ), w z = WithZero.exp (2 * n + 1) → Nm z d ∨ Nm z (d * Δ))
    {x y : K} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : ¬ Nm d x) (hy : ¬ Nm d y) : Nm d (x * y) := by sorry
