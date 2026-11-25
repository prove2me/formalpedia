-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_basis_descends_loc
-- name    : GlobalTheory.SectionBasis.basis_descends_loc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:17.379805+00:00
-- url     : https://prove2.me/theorems/369623f2-07cf-4f69-a07a-ec9dbaec2e35
-- title:
--   Section Basis: basis descends loc
-- statement:
--   The Section Basis construction uses the basis descends loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L412-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L412-L476

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
variable {K Kl K' : Type} [Field K] [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K'] [Algebra K K']
  [IsScalarTower K Kl K'] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem GlobalTheory.SectionBasis.basis_descends_loc {D D' N m n : ℕ} (hD : D = D') (e : Fin m ≃ Fin (N + 1)) (j0 : ι → Fin (N + 1))
    (v : ∀ Z, Fin m → Ω Z) (x : ∀ Z, Fin N → Ω Z)
    (hv : ∀ Z, v Z (e.symm (j0 Z)) ≠ 0)
    (hx : ∀ Z k, x Z k = v Z (e.symm ((j0 Z).succAbove k)) / v Z (e.symm (j0 Z)))
    (hind : ∀ Z, AlgebraicIndependent K (sImg (D := D) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z))))
      (OmS (Ω Z) D N))
    (t : Fin (D' + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (s : ∀ Z, Fin (D' + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω Z))
    (hs : ∀ Z i, s Z i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v Z k))
    (I : ∀ Z, Ideal (Localization.Away (s Z 0)))
    (hI : ∀ Z, I Z = Ideal.span (Set.range fun i : Fin D' =>
      algebraMap _ (Localization.Away (s Z 0)) (s Z i.succ) * IsLocalization.Away.invSelf (s Z 0)))
    (a : ∀ Z, K' →+* Localization.Away (s Z 0) ⧸ I Z)
    (ha : ∀ Z y, a Z y = Ideal.Quotient.mk (I Z) (algebraMap K' (Localization.Away (s Z 0)) y))
    (θ : Fin n → ∀ Z, Ω Z) (g : ∀ Z, Ω Z) (hg : ∀ Z, g Z ≠ 0)
    (w : Fin n → ∀ Z, Localization.Away (s Z 0) ⧸ I Z)
    (hw : ∀ k Z, w k Z * Ideal.Quotient.mk (I Z) (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))
        ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] g Z))) =
      Ideal.Quotient.mk (I Z) (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))
        ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] θ k Z))))
    (hli : ∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * w k Z = 0) → ∀ k, c k = 0)
    (hsp : ∀ y : ∀ Z, Localization.Away (s Z 0) ⧸ I Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * w k Z) :
    ∑ Z, Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) = n ∧
    (∀ p : Fin n → MvPolynomial (TVar D N) K,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z / g Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) D N, ∃ q : MvPolynomial (TVar D N) K, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar D N) K, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z / g Z)) := by sorry
