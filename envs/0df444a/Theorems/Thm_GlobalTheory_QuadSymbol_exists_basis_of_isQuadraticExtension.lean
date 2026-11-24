-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_exists_basis_of_isQuadraticExtension
-- name    : GlobalTheory.QuadSymbol.exists_basis_of_isQuadraticExtension
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:39.55221+00:00
-- url     : https://prove2.me/theorems/724ac28c-0d2e-43ae-b325-0eda2341c2cb
-- title:
--   Quad Symbol: exists basis of is Quadratic Extension
-- statement:
--   The Quad Symbol construction uses the exists basis of is Quadratic Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsBasisOfIsQuadraticExtension.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsBasisOfIsQuadraticExtension.lean#L10-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisOfIsQuadraticExtension
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

theorem GlobalTheory.QuadSymbol.exists_basis_of_isQuadraticExtension (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (e : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ := by sorry
