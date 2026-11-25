-- Prove2me | Theorems.Thm_GlobalTheory_T_generator_minpoly_eigenvalue_compat
-- name    : GlobalTheory.T.generator_minpoly_eigenvalue_compat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:43.368536+00:00
-- url     : https://prove2.me/theorems/7b5b502d-ce27-47fd-a3b0-d873256eda07
-- title:
--   T: generator minpoly eigenvalue compat
-- statement:
--   The T construction uses the generator minpoly eigenvalue compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeneratorMinpolyEigenvalueCompatStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeneratorMinpolyEigenvalueCompatStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeneratorMinpolyEigenvalueCompat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeneratorMinpolyEigenvalueCompatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.generator_minpoly_eigenvalue_compat : ∀ (E : Type) [Field E] [NumberField E] (V : Type 1) [AddCommGroup V] [Module ℂ V] (P : E →+ V),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (b : E) (T : Module.End ℂ V), (∀ x, T (P x) = P (b * x)) →
    IntermediateField.adjoin ℚ {b} = ⊤ →
    Polynomial.aeval T ((minpoly ℚ b).map (algebraMap ℚ ℂ)) = 0 ∧
    ∀ (σ : E →+* ℂ) (a : E) (S : Module.End ℂ V), (∀ x, S (P x) = P (a * x)) → ∀ y, T y = σ b • y → S y = σ a • y := by sorry
