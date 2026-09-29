-- Prove2me | Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits
-- name    : NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3e69417c-7264-54d4-96e9-e1722c3f40c2
-- title:
--   Coinduced local unit module is the product over places above v
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra and $K/E$ Galois, and let $v$ be a height-one prime of $\mathcal{O}_E$. Write $G = K \simeq_{\mathrm{alg}[E]} K$ for the Galois group, let [`NumberField.PlaceAbove.above E K v`](def/NumberField_PlaceAbove.html#L27) be the chosen height-one prime of $\mathcal{O}_K$ lying above $v$, let $D =$ [`NumberField.FiniteSIdele.D E K v`](def/NumberField_FiniteSIdeleModule.html#L15) be its decomposition subgroup in $G$, i.e. the decomposition subgroup of the valuation subring of the valuation attached to that prime, and let [`NumberField.FiniteSIdele.localUnits E K v`](def/NumberField_FiniteSIdeleModule.html#L20) be the $\mathbb{Z}$-representation of $D$ on the unit group of the adic completion of $K$ at that prime, coming from the multiplicative distributive action of $D$. The theorem asserts the existence of an isomorphism $e$ of additive groups from the coinduced representation `Rep.coind` of this $D$-representation along the inclusion $D \hookrightarrow G$ to the additive group underlying $\prod_{w} (K_w)^{\times}$, the product taken over all height-one primes $w$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_E$ equals $v$, with the following equivariance in coordinates: for every $g \in G$, every element $f$ of the coinduced representation, and all $w, w'$ in that index set together with a proof $h$ that $g \cdot w' = w$, the $w$-coordinate of $e(\rho(g) f)$ equals the image of the $w'$-coordinate of $e(f)$ under [`NumberField.PlaceTransport.transportUnits g h`](def/NumberField_PlaceTransport.html#L199), the multiplicative isomorphism $(K_{w'})^{\times} \to (K_w)^{\times}$ induced by the ring isomorphism of completions transported by $g$.
--
--   This is the Shapiro-type identification of the local factor of the finite idèle module at $v$: the coinduced module of the local units at a single chosen place above $v$ is identified, $G$-equivariantly, with the full product of unit groups of the completions at all places of $K$ above $v$, the Galois action being "move the place, then transport". It is used in the Herbrand-quotient computation of the Tate cardinality of the fibre box of the finite idèles at $v$ in terms of local degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits.lean

import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localUnits E K v))
          ≃+ Additive (Π w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                            w.under (NumberField.RingOfIntegers E) = v}, (w.1.adicCompletion K)ˣ),
      ∀ (g : K ≃ₐ[E] K) (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localUnits E K v))
        (w w' : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                  w.under (NumberField.RingOfIntegers E) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v)).ρ g f)) w
          = NumberField.PlaceTransport.transportUnits g h (Additive.toMul (e f) w') := by sorry
