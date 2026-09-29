-- Prove2me | Theorems.Thm_NumberField_SIdele_exists_hom_obj_ideles_injective_of_ideleGaloisDescent
-- name    : NumberField.SIdele.exists_hom_obj_ideles_injective_of_ideleGaloisDescent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/2913d7f7-d125-5113-975e-01c4bd0e72b1
-- title:
--   The S-idèle module as a Galois-equivariant embedding into the idèles
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, let $S$ be a finite set of height-one primes of $\mathcal{O}_E$, and let $D$ be an idèle Galois descent datum for $\mathcal{O}_K$, $E$, $K$, that is, a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $K \simeq_{\mathrm{alg}[E]} K$ to the ring automorphisms of $\mathrm{AdeleRing}\,(\mathcal{O}_K)\,K$, compatible with the structure map from $K$ in the sense that $D.\mathrm{act}\,g$ sends the image of $x \in K$ to the image of $g x$, and with each $D.\mathrm{act}\,g$ continuous. Assume a multiplicative distributive action of $K \simeq_{\mathrm{alg}[E]} K$ on the units $(\mathrm{AdeleRing}\,(\mathcal{O}_K)\,K)^{\times}$ is given which agrees with $D$, i.e. $g \bullet x = D.\mathrm{unitsAct}\,g\,x$ for all $g$ and all units $x$, where $D.\mathrm{unitsAct}\,g$ is the automorphism of the unit group induced by $D.\mathrm{act}\,g$. The assertion is the existence of a morphism $\Psi$ in $\mathrm{Rep}\,\mathbb{Z}\,(K \simeq_{\mathrm{alg}[E]} K)$ from [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) — the product representation over the family `fibre E K S` of local factors indexed by the finite and infinite decomposition data — to `Rep.ofMulDistribMulAction` of the unit group of the adèle ring, with three properties: the underlying map $\Psi.\mathrm{hom}$ is injective; a unit $y$ of the adèle ring lies in the image, in the sense that $\mathrm{Additive.ofMul}\,y = \Psi.\mathrm{hom}\,x$ for some $x$, exactly when $y$ belongs to [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51), i.e. when, for every height-one prime $w$ of $\mathcal{O}_K$ not lying under a prime of $S$, the $w$-component of the finite part of $y$ and that of $y^{-1}$ both lie in the $w$-adic valuation ring; and $\Psi$ carries the diagonal map [`NumberField.SIdele.diag E K S`](def/NumberField_SIdeleModule.html#L91) to principal idèles, namely $\mathrm{Additive.toMul}(\Psi.\mathrm{hom}((\mathrm{diag}\,E\,K\,S).\mathrm{hom}\,x))$ is the image of the unit $\mathrm{val}\,E\,K\,S\,x \in K^{\times}$ under the structure map $K \to \mathrm{AdeleRing}\,(\mathcal{O}_K)\,K$, for every $x$ in the $S$-unit representation [`NumberField.SUnits.sUnitsRep E K S`](def/NumberField_SUnitsModule.html#L52).
--
--   This identifies the $S$-idèle module of $K/E$, built as a product of local factors over the places of $K$, with the subgroup of idèles that are units outside the places above $S$, as an isomorphism onto that subgroup in the category of $\mathbb{Z}[\mathrm{Gal}(K/E)]$-modules, and records that the diagonal $S$-units map becomes the principal-idèle map. It is used in the cohomological computations that compare $H^2$ of the $S$-idèle and $S$-unit modules with $H^2$ of the idèles, in [`NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation`](thm.html#NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation) and [`NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le`](thm.html#NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_exists_hom_obj_ideles_injective_of_ideleGaloisDescent.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory groupCohomology

theorem NumberField.SIdele.exists_hom_obj_ideles_injective_of_ideleGaloisDescent
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x) :
    ∃ Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ,
      Function.Injective Ψ.hom ∧
      (∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
        y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Additive.toMul (Ψ.hom ((NumberField.SIdele.diag E K S).hom x)) =
        Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x)) := by sorry
