-- Prove2me | Theorems.Thm_GlobalTheory_Published_HasseNorm_local_of_global
-- name    : GlobalTheory.Published.HasseNorm.local_of_global
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:10.747287+00:00
-- url     : https://prove2.me/theorems/5bd4fb79-8966-4a5e-8ae1-10563ac7c74b
-- title:
--   Hasse Norm: local of global
-- statement:
--   The Hasse Norm construction uses the local of global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L328-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L328-L335

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
open GlobalTheory.Published.HasseNorm

theorem GlobalTheory.Published.HasseNorm.local_of_global {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type*) [CommRing A] [Algebra K A] {a : K} (h : ∃ x : L, Algebra.norm K x = a) :
    ∃ z : A ⊗[K] L, Algebra.norm A z = algebraMap K A a := by sorry
