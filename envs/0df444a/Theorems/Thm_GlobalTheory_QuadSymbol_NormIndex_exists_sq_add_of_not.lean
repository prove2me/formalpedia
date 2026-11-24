-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_exists_sq_add_of_not
-- name    : GlobalTheory.QuadSymbol.NormIndex.exists_sq_add_of_not
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:12:23.699164+00:00
-- url     : https://prove2.me/theorems/ca5a923a-11fa-4e1c-b373-7f01272e926b
-- title:
--   Norm Index: exists sq add of not
-- statement:
--   The Norm Index construction uses the exists sq add of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSquareMulInfinite.lean#L237-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSquareMulInfinite.lean#L237-L259

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

theorem GlobalTheory.QuadSymbol.NormIndex.exists_sq_add_of_not {k : Type} [Field k] [Finite k] (h2 : (2 : k) = 0) {a b : k}
    (ha : ∀ x, x ^ 2 + x ≠ a) (hb : ∀ x, x ^ 2 + x ≠ b) : ∃ x, x ^ 2 + x = a + b := by sorry
