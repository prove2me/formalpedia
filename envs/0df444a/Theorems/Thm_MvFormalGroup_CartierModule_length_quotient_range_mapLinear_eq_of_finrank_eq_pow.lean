-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_length_quotient_range_mapLinear_eq_of_finrank_eq_pow
-- name    : MvFormalGroup.CartierModule.length_quotient_range_mapLinear_eq_of_finrank_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/5e2917c7-44b8-5d76-a0bb-cf93fd147121
-- title:
--   Degree formula: colength of the Cartier module of an isogeny
-- statement:
--   Let $p$ be a prime, $k$ a perfect field of characteristic $p$, and $d$ a natural number. Let $\Psi$ and $\Phi$ be $d$-dimensional formal group laws over $k$, that is, $d$-tuples of power series in the $2d$ variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant coefficients, linear terms $X_i + Y_i$, and associative substitution, both assumed commutative in the sense that interchanging the two groups of variables fixes each component. Let $\psi \colon \Psi \to \Phi$ be a homomorphism, i.e. a $d$-tuple $(\psi_1,\dots,\psi_d)$ of power series in $X_1,\dots,X_d$ with zero constant coefficients satisfying $\psi \circ \Psi = \Phi(\psi \otimes \psi)$, and let $h$ be a natural number such that the quotient $k[[X_1,\dots,X_d]]/(\psi_1,\dots,\psi_d)$ has dimension exactly $p^h$ over $k$ (so in particular it is finite-dimensional). Then the quotient of $W(k)$-modules $M(\Phi)/\psi_* M(\Psi)$ has length $h$ over the Witt vectors $W(k)$, where $M(\Phi)$ denotes the Cartier module of $\Phi$ — the $d$-tuples of power series in the variables $X_0, X_1, \dots$ with zero constant coefficients that are additive for the Witt addition law with respect to $\Phi$ — and $\psi_*$ is the $W(k)$-linear map $M(\Psi) \to M(\Phi)$ given by substitution of a Cartier module element into $\psi$.
--
--   This is the degree formula for isogenies of commutative formal group laws over a perfect field of characteristic $p$: an isogeny of degree $p^h$ induces on Cartier–Dieudonné modules an inclusion of $W(k)$-lattices of colength $h$. It is used in the study of formal $O_D$-modules arising in the Čerednik–Drinfel'd setting, for instance to compute the lengths of the cokernels of isogenies of special formal $O_D$-modules and to deduce parity constraints on their heights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_length_quotient_range_mapLinear_eq_of_finrank_eq_pow.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.length_quotient_range_mapLinear_eq_of_finrank_eq_pow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ) (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ h) :
    Module.length (WittVector p k)
        (MvFormalGroup.CartierModule p Φ ⧸
          LinearMap.range (MvFormalGroup.CartierModule.mapLinear (p := p) ψ)) = h := by sorry
