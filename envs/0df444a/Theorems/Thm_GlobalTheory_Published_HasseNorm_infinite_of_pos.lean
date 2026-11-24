-- Prove2me | Theorems.Thm_GlobalTheory_Published_HasseNorm_infinite_of_pos
-- name    : GlobalTheory.Published.HasseNorm.infinite_of_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:56:43.257135+00:00
-- url     : https://prove2.me/theorems/49f25441-87dc-4a8e-b901-1c4ef42a0410
-- title:
--   Hasse Norm: infinite of pos
-- statement:
--   The Hasse Norm construction uses the infinite of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L339-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L339-L357

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.Published.HasseNorm.infinite_of_pos (a : maximalRealSubfield E) (ha : ∀ τ : E →+* ℂ, 0 < (τ a).re)
    (v : InfinitePlace (maximalRealSubfield E)) :
    ∃ z : v.Completion ⊗[maximalRealSubfield E] E,
      Algebra.norm v.Completion z = algebraMap (maximalRealSubfield E) v.Completion a := by sorry
