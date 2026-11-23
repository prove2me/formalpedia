-- Prove2me | Theorems.Thm_GlobalTheory_Published_norm_of_basis_one_sqrt
-- name    : GlobalTheory.Published.norm_of_basis_one_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:43.632183+00:00
-- url     : https://prove2.me/theorems/1be122ec-b56a-406b-badb-9b987e86a49c
-- title:
--   Published: norm of basis one sqrt
-- statement:
--   The Published construction uses the norm of basis one sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L220-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L220-L231

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

theorem GlobalTheory.Published.norm_of_basis_one_sqrt (b : Module.Basis (Fin 2) A S) (h0 : b 0 = 1) (d : A)
    (h1 : b 1 * b 1 = algebraMap A S d) (x y : A) :
    Algebra.norm A (x • b 0 + y • b 1) = x ^ 2 - d * y ^ 2 := by sorry
