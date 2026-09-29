-- Prove2me | Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits_transportUnits_apply
-- name    : NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits_transportUnits_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6381bcb5-b627-536f-8cbc-f445dee49ad0
-- title:
--   Coinduced local units at v as the product over w ∣ v
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an extension of $E$ that is Galois, write $G = K \simeq_{\mathrm{alg}[E]} K$ for its Galois group, and let $v$ be a height-one prime of $\mathcal{O}_E$. Let $w(v) =$ [`NumberField.PlaceAbove.above E K v`](def/NumberField_PlaceAbove.html#L27) be the chosen height-one prime of $\mathcal{O}_K$ above $v$, let $D =$ [`NumberField.FiniteSIdele.D E K v`](def/NumberField_FiniteSIdeleModule.html#L15) be the decomposition subgroup of $G$ attached to the valuation subring of the $w(v)$-adic valuation of $K$, and let [`NumberField.FiniteSIdele.localUnits E K v`](def/NumberField_FiniteSIdeleModule.html#L20) be the $\mathbb{Z}$-linear representation of $D$ on the unit group $(K_{w(v)})^\times$ of the $w(v)$-adic completion coming from its multiplicative $D$-action. The assertion is that there exists an isomorphism $e$ of additive groups from the representation of $G$ coinduced along the inclusion $D \hookrightarrow G$ of that representation, to the additive group attached to $\prod_{w} (K_w)^\times$, the product being over the height-one primes $w$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_E$ is $v$, such that for every element $f$ of the coinduced representation, every $y \in G$, every such $w$, and every proof that $y \cdot w = w(v)$, the image of the $w$-coordinate of $e(f)$ under the transport isomorphism $(K_w)^\times \xrightarrow{\sim} (K_{w(v)})^\times$ induced by $y$ equals the value $f(y)$ of the underlying function of $f$ at $y$.
--
--   This is the semilocal decomposition at $v$ in coinduced form: the $G$-module of $D$-equivariant functions $G \to (K_{w(v)})^\times$ is identified with the product of the local unit groups at the finitely many places of $K$ above $v$, together with the coordinatewise formula pinning the identification down (and not merely up to an automorphism of the coinduced module). It is used in the construction of the $S$-idèle modules, being cited by [`NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply`](thm.html#NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply) and [`NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport`](thm.html#NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits_transportUnits_apply.lean

import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits_transportUnits_apply (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localUnits E K v))
          ≃+ Additive (Π w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                            w.under (NumberField.RingOfIntegers E) = v}, (w.1.adicCompletion K)ˣ),
      ∀ (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localUnits E K v))
        (y : K ≃ₐ[E] K)
        (w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // w.under (NumberField.RingOfIntegers E) = v})
        (hy : y • w.1 = NumberField.PlaceAbove.above E K v),
        NumberField.PlaceTransport.transportUnits y hy (Additive.toMul (e f) w) = Additive.toMul (f.1 y) := by sorry
