-- Prove2me | Theorems.Thm_GlobalTheory_selfDual_lattices_one_genus
-- name    : GlobalTheory.selfDual_lattices_one_genus
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:02.171198+00:00
-- url     : https://prove2.me/theorems/4ed0cfa9-284c-4b02-bf52-9ab33c902369
-- title:
--   Global Theory: self Dual lattices one genus
-- statement:
--   The Global Theory construction uses the self Dual lattices one genus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L944-L982
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L944-L982

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
open GlobalTheory
open SelfDualGenus

theorem GlobalTheory.selfDual_lattices_one_genus {E : Type} [Field E] [NumberField E] [IsCMField E]
    [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (hG' : ∀ a b, cc (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hdual : ((∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y)) ∧
        ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm G' x y)) ∨
      ∃ ξ : E, ξ ≠ 0 ∧ cc ξ = -ξ ∧
        ((∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧
          ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y) ∧
        ((∀ x ∈ L', ∀ y ∈ L', ∃ k : ℤ, EFf ξ G' x y = k) ∧
          ∀ φ : L' →+ ℤ, ∃ x ∈ L', ∀ y : L', (φ y : ℚ) = EFf ξ G' x y)) :
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ∃ γ : GL (Fin r) (LocAlg v), IsLocalIsometry v G L G' L' γ) ∧
    (G' = G → ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (LocAlg v),
      (∀ v, IsLocalIsometry v G L G L' (γ v)) ∧ {v | γ v ≠ 1}.Finite) ∧
    (Published.Landherr → Published.HasseNormSt →
      ∀ Ψ : Set (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ) →
      (∀ τ ∈ Ψ, ∃ p : ℕ,
        (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
          gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
        ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
          gram τ G' Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) →
      ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) := by sorry
