-- Prove2me | Theorems.Thm_HorizontalPadicL_coprimeRamification_productFrobeniusClass_exists_v2
-- name    : HorizontalPadicL.coprimeRamification_productFrobeniusClass_exists_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:30:37.49464+00:00
-- url     : https://prove2.me/theorems/a828c85f-a967-48c6-8ed9-724ac87cb419
-- title:
--   Product automorphism and Chebotarev class from coprime ramification
-- statement:
--   Assume the standard facts that unramifiedness at a rational prime is preserved when taking the compositum of two number fields, and that every prime ramified in an $n$-th cyclotomic field divides $n$. Let the residual kernel discriminant be supported on $Np$, and let the seed conductor be coprime to $Np$. Then the residual--cyclotomic compositum is linearly disjoint from the seed cyclotomic field. The product automorphism which is trivial on the residual and $p^mN$-cyclotomic factors and realizes a chosen full-order seed value determines a Chebotarev class satisfying all fields of `SeededOrderlyFrobeniusClassData`.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 4.3, especially Lemma 4.14 and Corollary 4.15; standard discriminant criterion for linear disjointness and cyclotomic Artin reciprocity.

import Definitions.Def_KN_SeededPrimeGaloisDataV2
import Definitions.Def_KN_EigenformResidualGaloisRepresentationV2
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The remaining product-automorphism and Chebotarev step.

Assume the two standard discriminant facts needed in the argument: primes
unramified in two number fields remain unramified in their compositum, and a
prime ramified in an `n`-th cyclotomic field divides `n`.  If the residual
kernel discriminant is supported on `N * p` and the seed conductor is
coprime to `N * p`, then linear disjointness supplies the automorphism which
is trivial on the residual and `p ^ m * N` cyclotomic factors and has the
chosen full-order value on the seed factor.  Its Chebotarev class gives the
required seeded Frobenius data. -/
theorem coprimeRamification_productFrobeniusClass_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel)
    (m B : ℕ) (hB : 0 < B)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (V : SeededEigenformPadicPlaceData (p := p) f η)
    (D : EigenformResidualGaloisRepresentationData hN hk f V.embedding)
    (a : (ZMod η.1.1)ˣ)
    (ha : orderOf (η.2 (a : ZMod η.1.1)) = orderOf η.2)
    (hdiscr :
      letI : Field D.kernelField := D.kernelField_field
      letI : NumberField D.kernelField := D.kernelField_numberField
      ∀ {l : ℕ}, l.Prime →
        (l : ℤ) ∣ NumberField.discr D.kernelField → l ∣ N * p)
    (hsup : ∀ (K₁ K₂ : IntermediateField ℚ MTT.Qbar)
      [NumberField K₁] [NumberField K₂]
      {l : ℤ}, Prime l →
      ¬ l ∣ NumberField.discr K₁ →
      ¬ l ∣ NumberField.discr K₂ →
      letI : NumberField ↥(K₁ ⊔ K₂) :=
        { to_charZero := inferInstance
          to_finiteDimensional := IntermediateField.finiteDimensional_sup K₁ K₂ }
      ¬ l ∣ NumberField.discr ↥(K₁ ⊔ K₂))
    (hcyclo : ∀ (n : ℕ) [NeZero n]
      (K : IntermediateField ℚ MTT.Qbar) [NumberField K]
      [IsCyclotomicExtension {n} ℚ K]
      {l : ℕ}, l.Prime →
      (l : ℤ) ∣ NumberField.discr K → l ∣ n) :
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := by sorry

end HorizontalPadicL
