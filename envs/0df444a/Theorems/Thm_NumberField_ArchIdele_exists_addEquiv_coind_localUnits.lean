-- Prove2me | Theorems.Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits
-- name    : NumberField.ArchIdele.exists_addEquiv_coind_localUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/924dded5-e984-5da6-86b9-e89b83bf4f47
-- title:
--   Archimedean idèle fibre as coinduced local units
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra such that $K/E$ is Galois, write $G = K \simeq_{\mathrm{alg}[E]} K$ for its Galois group, and let $v$ be an infinite place of $E$. Let $w(v) =$ [`NumberField.ArchIdele.above E K v`](def/NumberField_ArchimedeanIdeleModule.html#L155) be the chosen infinite place of $K$ lying above $v$, let $D =$ [`NumberField.InfPlaceDecomp.decomp E K w(v)`](def/NumberField_ArchimedeanIdeleModule.html#L23) be the stabiliser of $w(v)$ in $G$ for the natural action, and let `localUnits` be the $\mathbb{Z}$-representation of $D$ given by the additive group of $(K_{w(v)})^{\times}$ with the $D$-action by multiplicative distributive automorphisms. The assertion is that there exists an additive isomorphism $e$ from the $G$-representation coinduced along the inclusion $D \hookrightarrow G$ to the additive group of $\prod_{w} (K_w)^{\times}$, the product being over the subtype of infinite places $w$ of $K$ with $w \circ \mathrm{algebraMap}\,E\,K = v$, such that $e$ intertwines the two actions in the following componentwise sense: for every $g \in G$, every element $f$ of the coinduced representation and all places $w, w'$ above $v$ with $g \cdot w' = w$, the $w$-component of $e(\rho(g) f)$ equals the image of the $w'$-component of $e(f)$ under [`NumberField.InfinitePlaceTransport.transportUnits g h`](def/NumberField_InfinitePlaceTransport.html#L58), i.e. under the unit group isomorphism $(K_{w'})^{\times} \simeq (K_{w})^{\times}$ induced by the ring isomorphism of completions $K_{w'} \simeq K_{w}$ coming from $g$ and the equality $g \cdot w' = w$.
--
--   This is the local-to-global comparison at an archimedean place: the factor of the idèle group attached to the fibre over $v$, presented as a module coinduced from the decomposition group of a single chosen place above $v$, is identified $G$-equivariantly with the product of the completed unit groups over all places of $K$ above $v$, the equivariance being "move the index, then transport". It is used in the computation of the Tate/Herbrand invariants of the infinite idèle fibre, in [`M4aHerbrand.infiniteIdeleFibre_tateCard_eq_localDegreeProd`](thm.html#M4aHerbrand.infiniteIdeleFibre_tateCard_eq_localDegreeProd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits.lean

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.ArchIdele.exists_addEquiv_coind_localUnits (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : NumberField.InfinitePlace E) :
    ∃ e : (Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))) ≃+
        Additive (Π w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v}, (w.1.Completion)ˣ),
      ∀ (g : K ≃ₐ[E] K)
        (f : Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
        (w w' : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v}) (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))).ρ g f)) w =
          NumberField.InfinitePlaceTransport.transportUnits g h (Additive.toMul (e f) w') := by sorry
