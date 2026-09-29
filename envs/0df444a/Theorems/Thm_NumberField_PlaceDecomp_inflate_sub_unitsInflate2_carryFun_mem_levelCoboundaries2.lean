-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
-- name    : NumberField.PlaceDecomp.inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8ae40ea7-cbc3-53f8-be00-334dcecbf996
-- title:
--   Inflated local class equals inflated carry cocycle modulo coboundaries
-- statement:
--   Fix a prime $p$ and a prime $q$, and an element $\zeta$ of $\overline{\mathbb Q}$ that is a primitive $p$-th root of unity; $\zeta$ and the hypothesis on it occur in no other hypothesis and not in the conclusion. The assertion is then: for every intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ that is a number field and Galois over $\mathbb Q$, every $w \in \mathrm{HeightOneSpectrum}(\mathcal O_F)$ with $p \mid \#D_w$, where $D_w =$ `decomp ℚ F w` is the decomposition subgroup in $F \simeq_{\mathbb Q} F$ of the valuation subring of $w$; for $q$-adic coordinates consisting of $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, a continuous ring homomorphism $\Phi : F_w \to \overline{\mathbb Q}_q$ with $\Phi(x) = \iota_q(\sigma x)$ on $F$ ($\iota_q$ being [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17)), and a surjective homomorphism $\pi : \mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q) \to D_w$ with $\pi\tau$ equal to the restriction of $\sigma^{-1}(\,\cdot\,)\sigma$ applied to `primeLocalToGlobal q τ` and with $\Phi(\pi\tau \cdot x) = \tau(\Phi x)$; for a bridge consisting of a finite extension $L'/\mathbb Q_q$ inside $\overline{\mathbb Q}_q$ carrying a $D_w$-action by ring automorphisms fixing $\mathbb Q_q$ and a compatible action on $(L')^\times$, a $D_w$-equivariant ring isomorphism $\Phi' : F_w \xrightarrow{\sim} L'$, a finite extension $K_0/\mathbb Q_q$ which is the $D_w$-fixed field inside $L'$ (that is, $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by every element of $D_w$), a morphism $\theta'$ of $D_w$-representations $(L')^\times \to F_w^\times$ induced by $\Phi'^{-1}$, and a class $u' \in H^2(D_w, (L')^\times)$ which is the local fundamental class in the sense of [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) (its image under any unramified overlayer datum is the inflation of the class of the associated carry cocycle on the uniformiser); for $m \in \mathbb Z$, a class $z \in H^2(D_w, F_w^\times)$ equal to $m \cdot \big((\#D_w/p)\cdot \theta'_*u'\big)$, a $2$-cocycle $x$ representing $z$, and a `levelCocycles₂` element $X$ for `primeLocalToGlobal q` and the representation of $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ on $\overline{\mathbb Q}_q^\times$ by $\mathbb Q_q$-algebra automorphisms, satisfying $X(g,h) = \Phi(x(\pi g, \pi h))$ on units; and finally, with $L_0 = \mathbb Q_q\big(\{x : x^{q^p-1}=1\}\big)$, normal over $\mathbb Q_q$, an automorphism $\varphi$ of $L_0$ generating all of its automorphism group in the sense that every automorphism is an integer power of $\varphi$, of finite order, and acting as $x \mapsto x^q$ on the $(q^p-1)$-st roots of unity, together with a unit $\alpha$ of $L_0$ whose image in $\overline{\mathbb Q}_q$ is $q^m$: the difference of $X$, read as a function of pairs of $\mathbb Q_q$-automorphisms of $\overline{\mathbb Q}_q$ with values in $\mathrm{Additive}\,\overline{\mathbb Q}_q^\times$, and `unitsInflate₂` applied to $L_0$ and the carry function `carryFun φ hs hfin (Additive.ofMul α)` — the function sending $(g,h)$ to $\alpha$ when $\mathrm{ord}(\varphi) \le \log_\varphi g + \log_\varphi h$ and to $0$ otherwise — lies in `levelCoboundaries₂ (localGaloisToGlobal q)` for that representation.
--
--   This is the cochain-level comparison of two normalisations of the local invariant at $q$: the canonical local fundamental class of $D_w$ acting on $F_w^\times$, transported through the $q$-adic coordinates, against the explicit carry cocycle on the unramified layer $\mathbb Q_q(\mu_{q^p-1})$ built from the arithmetic Frobenius and the uniformiser $q$, the two agreeing exactly (constant $+1$) modulo level coboundaries. It is used by [`NumberField.PlaceDecomp.localInv_eq_of_inflate_eq_kummer`](thm.html#NumberField.PlaceDecomp.localInv_eq_of_inflate_eq_kummer) to identify the local invariant with the Kummer-theoretic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2.lean

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

theorem NumberField.PlaceDecomp.inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
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

    (φ : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) ≃ₐ[ℚ_[q]] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (_ : ∀ x : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}), (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ))
    (α : ((IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))ˣ)
    (_ : ((α : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((q : ℚ_[q]) ^ m))
    (_ : Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})),
    (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) =>
        (show Additive (PadicAlgCl q)ˣ from
          (X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) g))
      - unitsInflate₂ (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
          (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) (Additive.ofMul α))
      ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by sorry
