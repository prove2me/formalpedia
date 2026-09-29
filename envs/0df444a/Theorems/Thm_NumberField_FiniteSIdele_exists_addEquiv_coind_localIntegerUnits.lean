-- Prove2me | Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits
-- name    : NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/9b24a3d5-e28b-5a08-a5dd-57f5e3ae9bdb
-- title:
--   Coinduced local integral units as the product over places above v
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra such that $K/E$ is Galois, and let $v$ be a height-one prime of $\mathcal{O}_E$. Write $w(v)$ for the prime [`NumberField.PlaceAbove.above E K v`](def/NumberField_PlaceAbove.html#L27) of $\mathcal{O}_K$ chosen above $v$, and let $D$ be [`NumberField.FiniteSIdele.D E K v`](def/NumberField_FiniteSIdeleModule.html#L15), the decomposition subgroup of $K \simeq_{\mathrm{alg}[E]} K$ attached to the valuation subring of the $w(v)$-adic valuation of $K$. The $\mathbb{Z}$-representation [`NumberField.FiniteSIdele.localIntegerUnits E K v`](def/NumberField_FiniteSIdeleModule.html#L23) of $D$ is the unit group $(\mathcal{O}_{K_{w(v)}})^{\times}$ of the $w(v)$-adic completion integers, made additive via its multiplicative distributive $D$-action, and `Rep.coind` along the inclusion of $D$ gives a representation of the full Galois group. The assertion is that there is an isomorphism $e$ of additive groups from this coinduced representation onto the additive group of $\prod_{w} (\mathcal{O}_{K_w})^{\times}$, the product taken over the subtype of height-one primes $w$ of $\mathcal{O}_K$ with $w$ lying under $v$ in $\mathcal{O}_E$, which is equivariant in the following componentwise sense: for every $g$ in the Galois group, every element $f$ of the coinduced module, every pair $w, w'$ in that fibre and every proof $h$ that $g \cdot w' = w$, the $w$-component of $e(\rho(g) f)$ equals [`NumberField.PlaceTransport.transportIntegerUnits g h`](def/NumberField_PlaceTransport.html#L205) applied to the $w'$-component of $e(f)$, where the latter is the isomorphism $(\mathcal{O}_{K_{w'}})^{\times} \simeq (\mathcal{O}_{K_{w}})^{\times}$ obtained by applying the units functor to the transport ring isomorphism induced by $g$.
--
--   This is the integral counterpart of the standard semilocal decomposition identifying a module coinduced from a decomposition subgroup with the product of the local data over all places above $v$, here for the unit groups of the completed local rings. It provides the local factors away from $S$ in the finite $S$-idèle module and is used in the Herbrand-quotient and cohomological-triviality computations for the integral boxes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits.lean

import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
          ≃+ Additive (Π w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                            w.under (NumberField.RingOfIntegers E) = v}, (w.1.adicCompletionIntegers K)ˣ),
      ∀ (g : K ≃ₐ[E] K) (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v))
        (w w' : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                  w.under (NumberField.RingOfIntegers E) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localIntegerUnits E K v)).ρ g f)) w
          = NumberField.PlaceTransport.transportIntegerUnits g h (Additive.toMul (e f) w') := by sorry
