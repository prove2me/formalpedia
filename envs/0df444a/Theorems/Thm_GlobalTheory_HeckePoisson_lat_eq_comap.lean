-- Prove2me | Theorems.Thm_GlobalTheory_HeckePoisson_lat_eq_comap
-- name    : GlobalTheory.HeckePoisson.lat_eq_comap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:07:28.679152+00:00
-- url     : https://prove2.me/theorems/e640fcd9-419e-4d2c-99c1-d2d9db7fb86f
-- title:
--   Hecke Poisson: lat eq comap
-- statement:
--   The Hecke Poisson construction uses the lat eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeIdealEuclideanLatticeIsZLattice.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeIdealEuclideanLatticeIsZLattice.lean#L62-L76

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
open Classical

theorem GlobalTheory.HeckePoisson.lat_eq_comap {φ : I → K →+* ℂ} (h : IsCMType φ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    lat φ M = ZLattice.comap (E := mixedEmbedding.mixedSpace K) (F := EuclideanSpace ℂ I) ℝ (mixedEmbedding.idealLattice K
      (Units.mk0 (M : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hM)))
      (toMixed h).toContinuousLinearEquiv.toLinearMap := by sorry
