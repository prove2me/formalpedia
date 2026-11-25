-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_exists_maps
-- name    : GlobalTheory.SectionBasis.exists_maps
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:51:53.275914+00:00
-- url     : https://prove2.me/theorems/6e16eae8-949d-44d6-9cab-7ff78abf341e
-- title:
--   Section Basis: exists maps
-- statement:
--   The Section Basis construction uses the exists maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L160-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L160-L263

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
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}

theorem GlobalTheory.SectionBasis.exists_maps (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) (t : TVar D N → K') (ht : AlgebraicIndependent K t)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    [FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    (hL : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom j0 x q)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) K']
    (hK : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) K' (algebraMap (MvPolynomial (TVar D N) K) _ q) = aeval t q)
    {Q : Type} [CommRing Q] (a : K' →+* Q) (ψ : Ω →+* Q)
    (hc : ∀ c : K, ψ (algebraMap K Ω c) = a (algebraMap K K' c))
    (hrel : ∀ i : Fin D, ∑ j, a (t (i.succ, j)) * ψ (v j) = 0)
    (huniv : ∀ (R : Type) [CommRing R] (a' : K' →+* R) (ψ' : Ω →+* R),
      (∀ c : K, ψ' (algebraMap K Ω c) = a' (algebraMap K K' c)) → IsUnit (∑ j, a' (t (0, j)) * ψ' (v j)) →
      (∀ i : Fin D, ∑ j, a' (t (i.succ, j)) * ψ' (v j) = 0) →
      ∃ g : Q →+* R, (∀ y, g (a y) = a' y) ∧ ∀ ω, g (ψ ω) = ψ' ω) :
    ∃ β : OmS Ω D N →+* Q, (∀ q : MvPolynomial (TVar D N) K, β (sHom j0 x q) = a (aeval t q)) ∧ (∀ ω, β (algebraMap Ω _ ω) = ψ ω) ∧
      ∃ α : Q →+* K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N,
        (∀ y, α (a y) = algebraMap K' _ y) ∧ Function.Surjective α := by sorry
