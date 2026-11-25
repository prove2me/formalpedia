-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_monic_base_polynomial_root_near_decomposition
-- name    : GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:04.470932+00:00
-- url     : https://prove2.me/theorems/09ab239e-ee62-4773-a596-b2afe371b2da
-- title:
--   T: exists monic base polynomial root near decomposition
-- statement:
--   The T construction uses the exists monic base polynomial root near decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicBasePolynomialRootNearDecompositionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicBasePolynomialRootNearDecompositionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicBasePolynomialRootNearDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicBasePolynomialRootNearDecompositionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by sorry
