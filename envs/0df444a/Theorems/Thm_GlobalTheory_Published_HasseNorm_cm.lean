-- Prove2me | Theorems.Thm_GlobalTheory_Published_HasseNorm_cm
-- name    : GlobalTheory.Published.HasseNorm.cm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:32.109083+00:00
-- url     : https://prove2.me/theorems/494adba9-4423-42fc-8b77-ec5723e1a06a
-- title:
--   Hasse Norm: cm
-- statement:
--   The Hasse Norm construction uses the cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L359-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L359-L371

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

theorem GlobalTheory.Published.HasseNorm.cm (H : HasseNorm) (a : maximalRealSubfield E) (ha : ∀ τ : E →+* ℂ, 0 < (τ a).re)
    (hf : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E,
        Algebra.norm (v.adicCompletion (maximalRealSubfield E)) z =
          algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) a) :
    ∃ x : E, (a : E) = x * cc x := by sorry
