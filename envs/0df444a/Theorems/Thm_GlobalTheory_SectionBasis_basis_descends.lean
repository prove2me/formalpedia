-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_basis_descends
-- name    : GlobalTheory.SectionBasis.basis_descends
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:52:13.973828+00:00
-- url     : https://prove2.me/theorems/d531b000-1107-4f3a-876f-6e507c5a41d5
-- title:
--   Section Basis: basis descends
-- statement:
--   The Section Basis construction uses the basis descends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L275-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L275-L379

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {D N : ℕ} {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem GlobalTheory.SectionBasis.basis_descends (j0 : ι → Fin (N + 1)) (v : ∀ Z, Fin (N + 1) → Ω Z) (x : ∀ Z, Fin N → Ω Z)
    (hv : ∀ Z, v Z (j0 Z) ≠ 0) (hx : ∀ Z k, x Z k = v Z ((j0 Z).succAbove k) / v Z (j0 Z))
    (hind : ∀ Z, AlgebraicIndependent K (sImg (D := D) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z))))
      (OmS (Ω Z) D N))
    (t : TVar D N → K') (ht : AlgebraicIndependent K t)
    {Q : ι → Type} [∀ Z, CommRing (Q Z)] (a : ∀ Z, K' →+* Q Z) (ψ : ∀ Z, Ω Z →+* Q Z)
    (hc : ∀ Z (c : K), ψ Z (algebraMap K (Ω Z) c) = a Z (algebraMap K K' c))
    (hrel : ∀ Z (i : Fin D), ∑ j, a Z (t (i.succ, j)) * ψ Z (v Z j) = 0)
    (huniv : ∀ Z (R : Type) [CommRing R] (a' : K' →+* R) (ψ' : Ω Z →+* R),
      (∀ c : K, ψ' (algebraMap K (Ω Z) c) = a' (algebraMap K K' c)) → IsUnit (∑ j, a' (t (0, j)) * ψ' (v Z j)) →
      (∀ i : Fin D, ∑ j, a' (t (i.succ, j)) * ψ' (v Z j) = 0) →
      ∃ g : Q Z →+* R, (∀ y, g (a Z y) = a' y) ∧ ∀ ω, g (ψ Z ω) = ψ' ω)
    {n : ℕ} (θ : Fin n → ∀ Z, Ω Z)
    (hli : ∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * ψ Z (θ k Z) = 0) → ∀ k, c k = 0)
    (hsp : ∀ y : ∀ Z, Q Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * ψ Z (θ k Z)) :
    ∑ Z, Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) = n ∧
    (∀ p : Fin n → MvPolynomial (TVar D N) K,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) D N, ∃ q : MvPolynomial (TVar D N) K, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar D N) K, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z)) := by sorry
