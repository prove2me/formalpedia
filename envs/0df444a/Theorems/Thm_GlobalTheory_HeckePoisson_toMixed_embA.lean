-- Prove2me | Theorems.Thm_GlobalTheory_HeckePoisson_toMixed_embA
-- name    : GlobalTheory.HeckePoisson.toMixed_embA
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:39.615057+00:00
-- url     : https://prove2.me/theorems/30fc9cfd-d2a8-4cbb-84e0-28eed794fc69
-- title:
--   Hecke Poisson: to Mixed emb A
-- statement:
--   The Hecke Poisson construction uses the to Mixed emb A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeIdealEuclideanLatticeIsZLattice.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeIdealEuclideanLatticeIsZLattice.lean#L44-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
noncomputable section
open GlobalTheory GlobalTheory.HeckePoisson
open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]

theorem GlobalTheory.HeckePoisson.toMixed_embA {φ : I → K →+* ℂ} (h : IsCMType φ) (α : 𝓞 K) :
    toMixed h (embA φ α) = mixedEmbedding K (α : K) := by sorry
