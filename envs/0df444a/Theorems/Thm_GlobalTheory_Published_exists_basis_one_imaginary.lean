-- Prove2me | Theorems.Thm_GlobalTheory_Published_exists_basis_one_imaginary
-- name    : GlobalTheory.Published.exists_basis_one_imaginary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:59.995135+00:00
-- url     : https://prove2.me/theorems/59aa5881-143f-4276-82b4-6324c9815e17
-- title:
--   Published: exists basis one imaginary
-- statement:
--   The Published construction uses the exists basis one imaginary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L259-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L259-L277

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.Published.exists_basis_one_imaginary {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) :
    ∃ b : Module.Basis (Fin 2) (maximalRealSubfield E) E, b 0 = 1 ∧ b 1 = θ := by sorry
