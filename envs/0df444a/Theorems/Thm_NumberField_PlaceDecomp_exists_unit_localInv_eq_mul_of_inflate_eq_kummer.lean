-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_unit_localInv_eq_mul_of_inflate_eq_kummer
-- name    : NumberField.PlaceDecomp.exists_unit_localInv_eq_mul_of_inflate_eq_kummer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/19b3c6d8-bed9-53e1-ac18-f568cd281b04
-- title:
--   Existence of a universal unit normalising the local invariant
-- statement:
--   Let $p$ be a prime, $q$ a prime, and $\zeta \in \overline{\mathbb Q}$ a primitive $p$-th root of unity. The assertion is that there is a unit $u \in (\mathbb Z/p)^{\times}$ such that the following holds for all data as follows. First, a level: an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ that is a number field, Galois over $\mathbb Q$, a height-one prime $w$ of $\mathcal O_F$ with $p \mid \#D_w$, where $D_w =$ `decomp ℚ ↥F w` is the decomposition subgroup in $\mathrm{Gal}(F/\mathbb Q)$ of the valuation subring of the $w$-adic valuation. Next, $q$-adic coordinates: $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, a continuous ring homomorphism $\Phi$ from the $w$-adic completion $F_w$ to $\overline{\mathbb Q}_q$ with $\Phi \circ \mathrm{alg} = \iota_q \circ \sigma$ on $F$, and a surjective homomorphism $\pi$ from $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ onto $D_w$ with $\pi(\tau)$ the restriction of $\sigma^{-1}\,\mathrm{res}(\tau)\,\sigma$ to $F$, such that $\Phi(\pi(\tau)\cdot x) = \tau(\Phi x)$. Next, a local layer: a finite intermediate field $L'$ of $\overline{\mathbb Q}_q/\mathbb Q_q$ with a $D_w$-action by semiring automorphisms fixing $\mathbb Q_q$ and a compatible action on $(L')^{\times}$, a $D_w$-equivariant ring isomorphism $\Phi' : F_w \cong L'$, a finite intermediate field $K_0$ which is a base for $L'$ in the sense that $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_w$, a morphism $\theta'$ of $D_w$-representations from $(L')^{\times}$ to $F_w^{\times}$ whose underlying map is $\Phi'^{-1}$, and a class $u' \in H^2(D_w, (L')^{\times})$ satisfying `IsLocalFundamentalClass` (the normalisation by unramified overlay data: for every overlayer datum, the pullback of $u'$ equals the inflation of the class of the carry cocycle of the Frobenius on the uniformiser). Next, $m \in \mathbb Z$ and a class $z \in H^2(D_w, F_w^{\times})$ with $z = m\cdot\big((\#D_w/p)\cdot \theta'_*u'\big)$, a $2$-cocycle $x$ representing $z$, and a level $2$-cocycle $X$ for $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ with values in $\overline{\mathbb Q}_q^{\times}$ given by $X(g,h) = \Phi(x(\pi g, \pi h))$. Finally, a level $2$-cocycle $et$ with values in $\mathbb Z/p$ twisted by the mod-$p$ cyclotomic character pulled back to the local group, and a level $2$-cocycle $E$ in $\overline{\mathbb Q}_q^{\times}$ with $E(g,h) = \iota_q(\zeta)^{\,et(g,h)}$, such that $X$ and $E$ have the same class in continuous $H^2$. Then $\mathrm{localInv}\,p\,\zeta\,q$ of the continuous class of $et$ equals $u \cdot m$ in $\mathbb Z/p$.
--
--   This records, in the form of one orientation unit quantified before all level data, the comparison between the normalisation of the local invariant $\mathrm{localInv}$ (fixed by its $\zeta$-carry condition on $H^2$ of the local Galois group with $\mu_p$-coefficients) and the normalisation of the local fundamental class of the layer $F_w/\mathbb Q_q$ by unramified overlay data. It is the local input for the place-by-place computation used by [`NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge`](thm.html#NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge) and its primary variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_unit_localInv_eq_mul_of_inflate_eq_kummer.lean

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

theorem NumberField.PlaceDecomp.exists_unit_localInv_eq_mul_of_inflate_eq_kummer
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ u : (ZMod p)ˣ,
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
    localInv p ζ q (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) et) = (u : ZMod p) * (m : ZMod p) := by sorry
