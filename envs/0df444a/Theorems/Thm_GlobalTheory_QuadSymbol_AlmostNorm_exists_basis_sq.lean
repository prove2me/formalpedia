-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_AlmostNorm_exists_basis_sq
-- name    : GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:03:09.28922+00:00
-- url     : https://prove2.me/theorems/8be8ae94-ae1a-4f71-a8fa-93d4c09094fc
-- title:
--   Almost Norm: exists basis sq
-- statement:
--   The Almost Norm construction uses the exists basis sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AlmostNormFinDiag.lean#L11-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AlmostNormFinDiag.lean#L11-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QuadSymbol

theorem GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (b : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ b 0 = 1 ∧
      b 1 * b 1 = algebraMap K L δ := by sorry
