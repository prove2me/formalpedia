-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
-- name    : NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b58df91a-56dc-5533-9a28-c7b54ba07a3d
-- title:
--   S-unit realisation of p-primary H² classes after capitulation
-- statement:
--   Let $E \subseteq K \subseteq K''$ be number fields, with $K/E$ and $K''/E$ Galois and the algebra structures forming a scalar tower, and let $S$ be a finite set of height-one primes of $\mathcal{O}_E$. Let $D$ be an idèle Galois descent datum for $K/E$, that is, a homomorphism from $K \simeq_{\text{alg}[E]} K$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal{O}_K, K)$ that is continuous in each component and compatible with $\mathrm{algebraMap}$ on $K$; assume the given multiplicative-distributive action of $\mathrm{Gal}(K/E)$ on the idèle units is the one induced by $D$ on units ($\mathtt{hactI}$). For each height-one prime $w$ of $\mathcal{O}_K$ let $\mathtt{prG}\,w$ be a morphism of representations of the decomposition subgroup $\mathrm{decomp}\,E\,K\,w$ of the valuation subring of $w$ from the restricted idèle-unit representation to $(K_w)^\times$, given on elements by the $w$-coordinate map $\mathrm{finPart}\,w$ of idèle units. Assume the action of $\mathrm{Gal}(K/E)$ on $K^\times$ is the natural one, $j$ is the morphism of representations induced by $K^\times \to (\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$, and $\mathtt{incl}$ is the morphism from the restriction of $K^\times$ along $\mathrm{AlgEquiv.restrictNormalHom}$ to $(K'')^\times$ induced by $\mathrm{algebraMap}\,K\,K''$. Let $p$ be a prime and assume capitulation in the form: every ideal $I$ of $\mathcal{O}_K$ with $I^{p^k} = (a)$ for some $k$ and some nonzero $a \in \mathcal{O}_K$ has principal extension to $\mathcal{O}_{K''}$. Finally, let $y \in H^2(\mathrm{Gal}(K/E), K^\times)$ satisfy $p^k \cdot y = 0$ for some $k$, and suppose that for every prime $w$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_E$ is not the underlying ideal of a member of $S$, the image of $y$ in $H^2(\mathrm{decomp}\,E\,K\,w, (K_w)^\times)$ under $H^2(j)$ followed by restriction along $\mathtt{prG}\,w$ vanishes. Then there are a $2$-cocycle $f$ valued in the $S$-unit subrepresentation $\mathrm{sUnitsRep}\,E\,K''\,S$ of $(K'')^\times$ and an exponent $k'$ such that the class of $f$ is killed by $p^{k'}$ and is carried by $\mathrm{toUnitsRep}$ to the image of $y$ under $H^2$ of $\mathtt{incl}$ along $\mathrm{AlgEquiv.restrictNormalHom}$.
--
--   This is the capitulation step in the comparison of $H^2$ of the multiplicative group with $H^2$ of $S$-units: a $p$-primary class whose idèle image has vanishing local components outside the primes over $S$ becomes, after passage to $K''$, representable by a $2$-cocycle with $S$-unit values. It feeds the construction of $S$-unit cocycles with prescribed local invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))

    [MulDistribMulAction (K ≃ₐ[E] K) Kˣ]
    (hactF : ∀ (g : (K ≃ₐ[E] K)) (a : Kˣ), ((g • a : Kˣ) : K) = g (a : K))
    (j : (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
    (hj : ∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a))

    (incl : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') K''ˣ))
    (hincl : ∀ a : Kˣ, incl.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K K'' : K →* K'') a))

    (p : ℕ) [Fact p.Prime]
    (hcap : ∀ (I : Ideal (𝓞 K)) (k : ℕ) (a : 𝓞 K), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 K) (𝓞 K''))).IsPrincipal)

    (y : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) 2) (k : ℕ) (hy : (p ^ k : ℤ) • y = 0)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom
        ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y) = 0) :
    ∃ (f : cocycles₂ (NumberField.SUnits.sUnitsRep E K'' S)) (k' : ℕ),
      (p ^ k' : ℤ) • (H2π _ f) = 0 ∧
      (groupCohomology.map (MonoidHom.id (K'' ≃ₐ[E] K'')) (NumberField.SUnits.toUnitsRep E K'' S) 2).hom (H2π _ f) =
        (groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) incl 2).hom y := by sorry
