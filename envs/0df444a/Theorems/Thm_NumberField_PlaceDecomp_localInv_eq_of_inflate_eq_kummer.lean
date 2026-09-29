-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_localInv_eq_of_inflate_eq_kummer
-- name    : NumberField.PlaceDecomp.localInv_eq_of_inflate_eq_kummer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/5facfa63-b056-50c4-bf3a-d7d785ec72ff
-- title:
--   Local invariant equals m for a Kummer-inflated fundamental class
-- statement:
--   Fix a prime $p$, a prime $q$ and $\zeta$ in $\overline{\mathbb Q}$ with $\zeta$ a primitive $p$-th root of unity. Let $F\subset\overline{\mathbb Q}$ be a number field Galois over $\mathbb Q$, $w$ a height-one prime of $\mathcal O_F$, and write $D_w$ for the decomposition subgroup of the valuation subring of $w$ inside $\mathrm{Gal}(F/\mathbb Q)$; assume $p\mid\#D_w$. Let $\sigma$ be an automorphism of $\overline{\mathbb Q}$, $\Phi$ a continuous ring homomorphism from the $w$-adic completion $F_w$ to $\overline{\mathbb Q}_q$ with $\Phi(x)=\iota_q(\sigma x)$ on $F$, and $\pi:\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)\to D_w$ a surjective homomorphism with $\pi\tau$ the restriction of $\sigma^{-1}\,\tau|_{\overline{\mathbb Q}}\,\sigma$ to $F$ and $\Phi(\pi\tau\cdot x)=\tau(\Phi x)$. Let $L'$ be a finite extension of $\mathbb Q_q$ in $\overline{\mathbb Q}_q$ carrying a $D_w$-action on $L'$ and on $(L')^\times$ fixing $\mathbb Q_q$, compatible on units, with a $D_w$-equivariant ring isomorphism $\Phi':F_w\cong L'$; let $K_0$ be a finite extension of $\mathbb Q_q$ with $K_0\le L'$ and $K_0\cap L'$ exactly the $D_w$-fixed points of $L'$; let $\theta'$ be the morphism of $D_w$-representations $(L')^\times\to F_w^\times$ induced by $(\Phi')^{-1}$, and $u'\in H^2(D_w,(L')^\times)$ a class satisfying the local fundamental class condition [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) relative to $K_0$. Let $m\in\mathbb Z$ and let $z\in H^2(D_w,F_w^\times)$ equal $m\cdot\bigl((\#D_w/p)\cdot\theta'_*u'\bigr)$, represented by a $2$-cocycle $x$. Let $X$ be a level $2$-cocycle for $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ with values in $\overline{\mathbb Q}_q^{\times}$ given by $X(g,h)=\Phi(x(\pi g,\pi h))$, let $et$ be a level $2$-cocycle with coefficients $\mathbb Z/p$ twisted by the mod $p$ cyclotomic character composed with $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)\to\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and let $E$ be the level $2$-cocycle with $E(g,h)=\iota_q(\zeta)^{\,et(g,h)}$ (exponent the canonical lift of $et(g,h)\in\mathbb Z/p$). If $X$ and $E$ have the same class in continuous $H^2$, then `localInv p ζ q` applied to the continuous class of $et$ equals the image of $m$ in $\mathbb Z/p$.
--
--   This is the normalisation statement matching the local invariant map at $q$, pinned down by the carry cocycle of arithmetic Frobenius together with the uniformiser $q$, against the invariant of the local fundamental class of $F_w/\mathbb Q$ read in $q$-adic coordinates; the constant is exactly $1$, with no extra orientation unit. It is used by [`NumberField.PlaceDecomp.exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq`](thm.html#NumberField.PlaceDecomp.exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq) and [`NumberField.PlaceDecomp.exists_unit_localInv_eq_mul_of_inflate_eq_kummer`](thm.html#NumberField.PlaceDecomp.exists_unit_localInv_eq_mul_of_inflate_eq_kummer) in the local bookkeeping of the dual Selmer group computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_localInv_eq_of_inflate_eq_kummer.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.localInv_eq_of_inflate_eq_kummer
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))

    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (_ : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (_ : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (_ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (_ : Function.Surjective π)
    (_ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))

    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
    (Φ' : w.adicCompletion ↥F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ' (g • x) = g • Φ' x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
    (θ' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ'.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u')

    (m : ℤ) (z : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) 2)
    (_ : z = m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p) •
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u'))
    (x : cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) (_ : (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom x = z)
    (X : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (_ : ∀ g h : primeLocalGaloisGroup q, Additive.toMul ((X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) → Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h))))

    (et : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (E : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (_ : ∀ g h : primeLocalGaloisGroup q, ((Additive.toMul ((E : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ (((et : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h) : ZMod p).val))

    (_ : continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) X = continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) E),
    localInv p ζ q (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) et) = (m : ZMod p) := by sorry
