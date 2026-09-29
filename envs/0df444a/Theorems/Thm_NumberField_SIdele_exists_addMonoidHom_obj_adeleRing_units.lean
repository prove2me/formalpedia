-- Prove2me | Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units
-- name    : NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c4b187f1-b263-54ee-9916-83d1736b1dea
-- title:
--   Equivariant realisation of the S-idèle module inside A_K^×
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an extension of $E$ that is Galois, let $S$ be a finite set of height-one primes of $\mathcal{O}_E$, and let $D$ be an idèle Galois descent datum for $(\mathcal{O}_K, E, K)$, that is, a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $K \simeq_{\mathrm{alg}[E]} K$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal{O}_K, K)$ which fixes the image of $K$ in the sense that $D.\mathrm{act}\,g$ carries $\mathrm{algebraMap}\,x$ to $\mathrm{algebraMap}(g x)$, each $D.\mathrm{act}\,g$ being continuous. Then there is an additive group homomorphism $\Phi$ from the $\mathbb{Z}$-representation [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) of $K \simeq_{\mathrm{alg}[E]} K$ — the product, over the index family of `fibre E K S`, of that family of representations — to the idèle group $(\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$ written additively, such that: $\Phi$ is injective; the range of $\Phi$ is the additive subgroup attached to [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51), namely the group of adelic units $\delta$ whose finite component satisfies, at every height-one prime $w$ of $\mathcal{O}_K$ not lying under a member of $S$, that both $\delta_w$ and $(\delta^{-1})_w$ lie in the valuation ring of $w$; $\Phi$ is equivariant, $\Phi(\rho(g)x) = D.\mathrm{unitsAct}\,g\,(\Phi x)$ where $D.\mathrm{unitsAct}\,g$ is the automorphism of the unit group induced by $D.\mathrm{act}\,g$; and $\Phi$ composed with the diagonal map [`NumberField.SIdele.diag E K S`](def/NumberField_SIdeleModule.html#L91) from the $S$-unit representation sends $x$ to the image of the unit [`NumberField.SUnits.val E K S x`](def/NumberField_SUnitsModule.html#L78) of $K$ under the principal-idèle map $\mathrm{algebraMap}\,K\,\mathrm{AdeleRing}(\mathcal{O}_K,K)$.
--
--   This is the $\mathrm{Gal}(K/E)$-equivariant identification of the abstract $S$-idèle module with the subgroup of idèles that are units outside the places of $K$ above $S$, phrased for an arbitrary idèle Galois descent datum rather than for one fixed action. It is used in the identification of the quotient of the $S$-idèle module by the $S$-units with the idèle class group, through [`NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq`](thm.html#NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K) :
    ∃ Φ : (NumberField.SIdele.obj E K S) →+ Additive (AdeleRing (𝓞 K) K)ˣ,
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
        Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x)))) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) := by sorry
