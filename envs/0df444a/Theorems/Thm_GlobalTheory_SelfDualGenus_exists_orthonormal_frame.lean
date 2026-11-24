-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualGenus_exists_orthonormal_frame
-- name    : GlobalTheory.SelfDualGenus.exists_orthonormal_frame
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:11:07.711356+00:00
-- url     : https://prove2.me/theorems/ef95cb02-d2e8-4d54-87b1-3dedb1d2b01c
-- title:
--   Self Dual Genus: exists orthonormal frame
-- statement:
--   The Self Dual Genus construction uses the exists orthonormal frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L831-L843
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L831-L843

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
variable {G G' : Matrix (Fin r) (Fin r) E} {L L' : Submodule (𝓞 E) (Fin r → E)}
variable [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {𝔟 : FractionalIdeal (𝓞 E)⁰ E}

theorem GlobalTheory.SelfDualGenus.exists_orthonormal_frame (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ h : GL (Fin r) (LocAlg v),
      (h : Matrix (Fin r) (Fin r) (LocAlg v))ᵀ * G.map (locEmb v) *
        (h : Matrix (Fin r) (Fin r) (LocAlg v)).map (locConj v) = 1 ∧
      ∀ x, x ∈ locLattice v L ↔
        ∀ i, (((h⁻¹ : GL (Fin r) (LocAlg v)) : Matrix (Fin r) (Fin r) (LocAlg v)) *ᵥ x) i ∈
          locOrder v := by sorry
