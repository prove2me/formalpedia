-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_almostNorm_finDiag
-- name    : GlobalTheory.QuadSymbol.almostNorm_finDiag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:34.249628+00:00
-- url     : https://prove2.me/theorems/f7955e45-30bb-4b7b-a362-21ff6cdb8c36
-- title:
--   Quad Symbol: almost Norm fin Diag
-- statement:
--   The Quad Symbol construction uses the almost Norm fin Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AlmostNormFinDiag.lean#L31-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AlmostNormFinDiag.lean#L31-L49

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

theorem GlobalTheory.QuadSymbol.almostNorm_finDiag :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L], ∀ t : Kˣ, AlmostNorm K L (finDiag K t) := by sorry
