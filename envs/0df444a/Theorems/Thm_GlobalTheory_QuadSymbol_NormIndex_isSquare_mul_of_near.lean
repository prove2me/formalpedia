-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_isSquare_mul_of_near
-- name    : GlobalTheory.QuadSymbol.NormIndex.isSquare_mul_of_near
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:25.472034+00:00
-- url     : https://prove2.me/theorems/40777161-95c4-4206-9dd2-1b0398d34887
-- title:
--   Norm Index: is Square mul of near
-- statement:
--   The Norm Index construction uses the is Square mul of near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSquareMulInfinite.lean#L265-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSquareMulInfinite.lean#L265-L321

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
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.QuadSymbol.NormIndex.isSquare_mul_of_near {x y : v.adicCompletion F} (hx : Valued.v x = 1) (hy : Valued.v y = 1)
    (hx4 : Valued.v (x - 1) ≤ Valued.v (4 : v.adicCompletion F))
    (hy4 : Valued.v (y - 1) ≤ Valued.v (4 : v.adicCompletion F))
    (hx' : ¬ IsSquare x) (hy' : ¬ IsSquare y) : IsSquare (x * y) := by sorry
