-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_hasLocalInv_map_of_ringEquiv
-- name    : NumberField.IdeleLocalInv.hasLocalInv_map_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/614ea89e-ca51-59a9-90dd-0c5378fc57e9
-- title:
--   Transport of a local invariant along an isomorphism of Galois layers
-- statement:
--   Let $K/E$ and $K'/E'$ be Galois extensions of number fields. Suppose given ring isomorphisms $e_0 : E \cong E'$ and $e : K \cong K'$ with $e(x) = e_0(x)$ on $E$ (i.e. $e$ commutes with the structure maps), a group isomorphism $c : \mathrm{Gal}(K/E) \cong \mathrm{Gal}(K'/E')$ with $c(g)(e\,y) = e(g\,y)$, height-one primes $v$ of $\mathcal O_E$ and $v'$ of $\mathcal O_{E'}$ with $|e_0 x|_{v'} = |x|_v$ for all $x \in E$, a map $pl$ from the height-one spectrum of $\mathcal O_K$ to that of $\mathcal O_{K'}$ with $|e\,y|_{pl(w)} = |y|_w$ for all $y \in K$, such that $c$ carries the decomposition subgroup $\mathrm{decomp}(E,K,w)$ (the decomposition subgroup over $E$ of the valuation subring of the $w$-adic valuation of $K$) into $\mathrm{decomp}(E',K',pl(w))$, and ring isomorphisms $T_w : K_w \cong K'_{pl(w)}$ of adic completions which extend $e$ on $K$ and satisfy $T_w(g \cdot y) = c(g) \cdot T_w(y)$ for $g$ in the decomposition group at $w$. Suppose further given idèle Galois descent data $D$ on $\mathbb A_K$ and $D'$ on $\mathbb A_{K'}$ (monoid homomorphisms from the Galois group to ring automorphisms of the adèle ring, compatible with the structure map from the field and continuous) whose induced actions on the unit groups coincide with the ambient multiplicative-distributive actions, and a morphism $\psi$ of representations from the restriction along $c^{-1}$ of $(\mathbb A_K)^\times$ to $(\mathbb A_{K'})^\times$ whose $pl(w)$-component is $T_w$ applied to the $w$-component, where components are taken by `finPart`, the projection of an idèle unit to the finite part followed by evaluation at the given prime. Let $x \in H^2(\mathrm{Gal}(K/E), (\mathbb A_K)^\times)$ and $t \in \mathbb Q/\mathbb Z$. The assertion is: if `HasLocalInv` holds for $(E,K,D,x,v,t)$, then it holds for $(E',K',D',\,H^2(c^{-1},\psi)(x),\,v',\,t)$, where the map on cohomology is `groupCohomology.map` applied to $c^{-1}$ and $\psi$ in degree $2$. Here `HasLocalInv` $(E,K,D,x,v,t)$ asserts the existence of: coordinate morphisms $prG_w$ of representations of the decomposition groups realising `finPart`; a prime $w$ of $\mathcal O_K$ contracting to $v$; a rational prime $q \in w$; a finite extension $L'$ of $\mathbb Q_q$ inside a fixed algebraic closure, carrying a faithful action of the decomposition group $D_w$ fixing $\mathbb Q_q$ pointwise and compatible with its action on $L'^\times$; a $D_w$-equivariant ring isomorphism $\Phi : K_w \cong L'$ and a morphism $\theta$ of representations realising $\Phi^{-1}$ on unit groups; a finite extension $K_0$ of $\mathbb Q_q$ which is the $D_w$-fixed base of $L'$ in the sense of [`ExtCitation.LocalLevel.IsBase`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13); a class $u' \in H^2(D_w, L'^\times)$ which is a local fundamental class in the sense of [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60); and an integer $n$ such that the image of $x$ in $H^2(D_w, K_w^\times)$ under restriction to $D_w$ along $prG_w$ equals $n$ times the image of $u'$ under $\theta$, and $t$ is the class of $n/\lvert D_w\rvert$ in $\mathbb Q/\mathbb Z$.
--
--   This is the functoriality, or transport of structure, statement for the local invariant at a finite place of a degree-two idèle cohomology class: an isomorphism of Galois layers together with matching transport data for places, decomposition groups, completions and idèles carries a class with local invariant $t$ at $v$ to a class with the same invariant at the corresponding place $v'$. It is used by [`NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv`](thm.html#NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv), where the special case $E = E'$, $K = K'$ and $e$ a field automorphism gives the invariance of the local invariants under conjugation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_hasLocalInv_map_of_ringEquiv.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.hasLocalInv_map_of_ringEquiv
    (E K E' K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    [Field E'] [NumberField E'] [Field K'] [NumberField K'] [Algebra E' K'] [IsGalois E' K']

    (e₀ : E ≃+* E') (e : K ≃+* K') (he : ∀ x : E, e (algebraMap E K x) = algebraMap E' K' (e₀ x))
    (c : (K ≃ₐ[E] K) ≃* (K' ≃ₐ[E'] K')) (hc : ∀ (g : K ≃ₐ[E] K) (y : K), c g (e y) = e (g y))

    (v : HeightOneSpectrum (𝓞 E)) (v' : HeightOneSpectrum (𝓞 E')) (hv : ∀ x : E, v'.valuation E' (e₀ x) = v.valuation E x)
    (pl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K'))
    (hpl : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), (pl w).valuation K' (e y) = w.valuation K y)
    (hcd : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : K ≃ₐ[E] K), g ∈ NumberField.PlaceDecomp.decomp E K w → c g ∈ NumberField.PlaceDecomp.decomp E' K' (pl w))

    (Tc : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K ≃+* (pl w).adicCompletion K')
    (hTc : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), Tc w (y : w.adicCompletion K) = ((e y : K') : (pl w).adicCompletion K'))
    (hTcs : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K),
      Tc w (g • y) = (⟨c g, hcd w g g.2⟩ : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) • Tc w y)

    (D : IdeleGaloisDescent (𝓞 K) E K) [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z)
    (D' : IdeleGaloisDescent (𝓞 K') E' K') [MulDistribMulAction (K' ≃ₐ[E'] K') (AdeleRing (𝓞 K') K')ˣ]
    (hactI' : ∀ (g : K' ≃ₐ[E'] K') (z : (AdeleRing (𝓞 K') K')ˣ), g • z = D'.unitsAct g z)
    (ψ : Rep.res c.symm.toMonoidHom (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
      Rep.ofMulDistribMulAction (K' ≃ₐ[E'] K') (AdeleRing (𝓞 K') K')ˣ)
    (hψ : ∀ (w : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ),
      finPart (pl w) (Additive.toMul (ψ.hom (Additive.ofMul z))) = Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K') (finPart w z))

    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2) (t : AddCircle (1 : ℚ))
    (h : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t) :
    NumberField.IdeleLocalInv.HasLocalInv E' K' D' hactI' ((groupCohomology.map c.symm.toMonoidHom ψ 2).hom x) v' t := by sorry
