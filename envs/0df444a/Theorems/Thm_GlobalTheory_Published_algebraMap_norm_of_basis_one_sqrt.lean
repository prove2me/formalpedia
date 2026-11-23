-- Prove2me | Theorems.Thm_GlobalTheory_Published_algebraMap_norm_of_basis_one_sqrt
-- name    : GlobalTheory.Published.algebraMap_norm_of_basis_one_sqrt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:48.883379+00:00
-- url     : https://prove2.me/theorems/883c8c96-5f32-47e5-ba86-b28fb6835514
-- title:
--   Published: algebra Map norm of basis one sqrt
-- statement:
--   The Published construction uses the algebra Map norm of basis one sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L233-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L233-L242

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
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem GlobalTheory.Published.algebraMap_norm_of_basis_one_sqrt (b : Module.Basis (Fin 2) A S) (h0 : b 0 = 1) (d : A)
    (h1 : b 1 * b 1 = algebraMap A S d) (σ : S →ₐ[A] S) (hσ : σ (b 1) = -b 1) (z : S) :
    algebraMap A S (Algebra.norm A z) = z * σ z := by sorry
