-- Prove2me | Theorems.Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply
-- name    : NumberField.ArchIdele.exists_addEquiv_coind_localUnits_transportUnits_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/58359b25-129c-503d-88d4-f76df8c3594e
-- title:
--   Coinduced archimedean units as the product over places above v
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra which is Galois over $E$, and let $v$ be an infinite place of $E$. Write $w_0 =$ [`NumberField.ArchIdele.above E K v`](def/NumberField_ArchimedeanIdeleModule.html#L155) for the chosen infinite place of $K$ above $v$, $D =$ [`NumberField.InfPlaceDecomp.decomp E K w_0`](def/NumberField_ArchimedeanIdeleModule.html#L23) for its stabiliser in $K \simeq_{\mathrm{alg}[E]} K$ under the action on infinite places, and `localUnits E K w_0` for the $\mathbb{Z}$-representation of $D$ obtained from the multiplicative action of $D$ on the unit group $(K_{w_0})^\times$ of the completion at $w_0$. The assertion is that there exists an isomorphism $e$ of additive groups from the representation coinduced along the inclusion $D \hookrightarrow \mathrm{Gal}(K/E)$ of this representation to the additive group underlying $\prod_{w \mid v} (K_w)^\times$, the product being over the subtype of infinite places $w$ of $K$ whose comap along $E \to K$ is $v$, such that the following coordinate formula holds: for every element $f$ of the coinduced representation, every $y : K \simeq_{\mathrm{alg}[E]} K$, every $w$ above $v$ and every proof that $y \cdot w = w_0$, the transport of units $(K_w)^\times \simeq (K_{w_0})^\times$ along $y$ (the unit group map induced by the completion of the ring isomorphism given by $y$, matching the absolute values of $w$ and $w_0$) sends the $w$-coordinate of $e(f)$ to the value $f(y)$ of the coinduced function at $y$.
--
--   This identifies the semilocal archimedean unit group at $v$, $\prod_{w\mid v}(K_w)^\times$, with the representation coinduced from the decomposition group at the chosen place $w_0$ above $v$, and pins the isomorphism down by giving each coordinate explicitly in terms of transport along a Galois element carrying $w$ to $w_0$ — a normalisation strictly stronger than mere additive equivariance. It is used in the construction of the archimedean part of the $S$-idèle module, in [`NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply`](thm.html#NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply) and [`NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport`](thm.html#NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply.lean

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.ArchIdele.exists_addEquiv_coind_localUnits_transportUnits_apply (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (v : NumberField.InfinitePlace E) :
    ∃ e : (Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))) ≃+
        Additive (Π w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v}, (w.1.Completion)ˣ),
      ∀ (f : Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
        (y : K ≃ₐ[E] K) (w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v})
        (hy : y • w.1 = NumberField.ArchIdele.above E K v),
        NumberField.InfinitePlaceTransport.transportUnits y hy (Additive.toMul (e f) w) = Additive.toMul (f.1 y) := by sorry
