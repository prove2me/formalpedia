-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualGenus_exists_eq_transpose_mul_map_locConj
-- name    : GlobalTheory.SelfDualGenus.exists_eq_transpose_mul_map_locConj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:52:48.048001+00:00
-- url     : https://prove2.me/theorems/401f9043-49c7-4f61-b901-2fa266413448
-- title:
--   Self Dual Genus: exists eq transpose mul map loc Conj
-- statement:
--   The Self Dual Genus construction uses the exists eq transpose mul map loc Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L570-L599
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L570-L599

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem GlobalTheory.SelfDualGenus.exists_eq_transpose_mul_map_locConj {M N : Matrix (Fin r) (Fin r) (LocAlg v)}
    (hM : ∀ i j, M i j ∈ locOrder v) (hN : ∀ i j, N i j ∈ locOrder v) (hMN : M * N = 1)
    (hh : ∀ i j, locConj v (M i j) = M j i) :
    ∃ P : GL (Fin r) (LocAlg v),
      (∀ i j, (P : Matrix (Fin r) (Fin r) (LocAlg v)) i j ∈ locOrder v) ∧
      (∀ i j, ((P⁻¹ : GL (Fin r) (LocAlg v)) : Matrix (Fin r) (Fin r) (LocAlg v)) i j ∈
        locOrder v) ∧
      M = (P : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ *
        (P : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) := by sorry
