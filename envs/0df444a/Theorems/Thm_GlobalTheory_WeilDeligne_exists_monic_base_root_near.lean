-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_exists_monic_base_root_near
-- name    : GlobalTheory.WeilDeligne.exists_monic_base_root_near
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:01.947747+00:00
-- url     : https://prove2.me/theorems/94b21fa9-1b44-51c0-92a1-54f6b498aef5
-- title:
--   Weil Deligne: exists monic base root near
-- statement:
--   The Weil Deligne construction uses the exists monic base root near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicBasePolynomialRootNearDecomposition.lean#L7-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicBasePolynomialRootNearDecomposition.lean#L7-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicBasePolynomialRootNearDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.exists_monic_base_root_near : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by sorry
