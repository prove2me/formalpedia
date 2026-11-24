-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualGenus_one_genus_of_modular
-- name    : GlobalTheory.SelfDualGenus.one_genus_of_modular
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:53:14.448181+00:00
-- url     : https://prove2.me/theorems/00e5838c-1aee-41de-a875-9fa1eb37693c
-- title:
--   Self Dual Genus: one genus of modular
-- statement:
--   The Self Dual Genus construction uses the one genus of modular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L804-L816
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L804-L816

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

theorem GlobalTheory.SelfDualGenus.one_genus_of_modular (h𝔟 : 𝔟 ≠ 0) (hc : ∀ z ∈ 𝔟, cc z ∈ 𝔟)
    (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟) (hmod' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', herm G x y ∈ 𝔟) :
    ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (LocAlg v),
      (∀ v, IsLocalIsometry v G L G L' (γ v)) ∧ {v | γ v ≠ 1}.Finite := by sorry
