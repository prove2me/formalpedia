-- Prove2me | Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply
-- name    : NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/e05f662a-0333-5aeb-9407-6b5a908c292e
-- title:
--   Coinduced local integral units as the product over w ∣ v
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra and $K/E$ Galois, and let $v$ be a height-one prime of $\mathcal O_E$. Write $w(v) =$ [`NumberField.PlaceAbove.above E K v`](def/NumberField_PlaceAbove.html#L27) for the chosen height-one prime of $\mathcal O_K$ above $v$, let $D =$ [`NumberField.FiniteSIdele.D E K v`](def/NumberField_FiniteSIdeleModule.html#L15) be its decomposition subgroup inside $K \simeq_{\mathrm{alg}[E]} K$, that is, the decomposition subgroup of the valuation subring of the $w(v)$-adic valuation, and let `localIntegerUnits E K v` be the $\mathbb Z$-linear representation of $D$ on $\bigl(\mathcal O_{w(v)}\bigr)^\times$, the units of the ring of integers of the $w(v)$-adic completion of $K$, coming from the multiplicative action of $D$. The assertion is that there exists an isomorphism $e$ of additive groups from the representation coinduced along the inclusion $D \hookrightarrow K \simeq_{\mathrm{alg}[E]} K$ of `localIntegerUnits E K v` onto the additive version of $\prod_{w} (\mathcal O_w)^\times$, the product over the height-one primes $w$ of $\mathcal O_K$ whose contraction to $\mathcal O_E$ is $v$, such that for every element $f$ of the coinduced representation, every $y \in K \simeq_{\mathrm{alg}[E]} K$, every such $w$ and every proof that $y \cdot w = w(v)$, the transport [`NumberField.PlaceTransport.transportIntegerUnits`](def/NumberField_PlaceTransport.html#L205) along $y$ of the $w$-coordinate of $e(f)$ equals the value $f(y)$, both read multiplicatively.
--
--   This identifies the coinduced module $\mathrm{Coind}_D^{\mathrm{Gal}(K/E)} \mathcal O_{w(v)}^\times$ with the semilocal unit group $\prod_{w \mid v} \mathcal O_w^\times$, together with the coordinatewise formula pinning the isomorphism down rather than merely asserting equivariance. It is used in the description of the units of the adèle ring as a Galois module, in [`NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply`](thm.html#NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply) and [`NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport`](thm.html#NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport), where the image of a diagonally embedded $S$-unit at the places above a prime outside $S$ must be computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply.lean

import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits_transportIntegerUnits_apply (E K : Type) [Field E]
    [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
          ≃+ Additive (Π w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                            w.under (NumberField.RingOfIntegers E) = v}, (w.1.adicCompletionIntegers K)ˣ),
      ∀ (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
        (y : K ≃ₐ[E] K)
        (w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // w.under (NumberField.RingOfIntegers E) = v})
        (hy : y • w.1 = NumberField.PlaceAbove.above E K v),
        NumberField.PlaceTransport.transportIntegerUnits y hy (Additive.toMul (e f) w) = Additive.toMul (f.1 y) := by sorry
