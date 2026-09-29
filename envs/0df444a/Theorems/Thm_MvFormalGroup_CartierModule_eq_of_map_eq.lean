-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_eq_of_map_eq
-- name    : MvFormalGroup.CartierModule.eq_of_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/9ed4bf33-bdca-5871-a805-7a4b8c2b8d09
-- title:
--   Faithfulness of the Cartier module functor in characteristic p
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring of characteristic $p$, and $d,d'$ natural numbers. Let $\Phi$ be a $d$-dimensional formal group law over $R$ and $\Phi'$ a $d'$-dimensional one: each is a tuple of power series in two blocks of variables, with vanishing constant coefficients, linear coefficients giving the identity in each block, and satisfying the associativity identity; both are assumed commutative in the sense that interchanging the two blocks of variables fixes every component. Let $\varphi,\psi\colon\Phi\to\Phi'$ be homomorphisms, i.e. $d'$-tuples of power series in $d$ variables with zero constant coefficients satisfying $\varphi(\Phi(X,Y))=\Phi'(\varphi(X),\varphi(Y))$. The Cartier module [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) consists of the $d$-tuples $f$ of power series in variables indexed by $\mathbb{N}$, with zero constant coefficients, such that substituting the Witt addition laws `WittLaw.addFam p R` (the images over $R$ of the polynomials `WittVector.wittAdd p n`) into $f$ gives $\Phi$ applied to the two blockwise copies of $f$; [`MvFormalGroup.CartierModule.map`](def/MvFormalGroup_CartierModule.html#L739) sends such an $f$ to the tuple $(\varphi\circ f)$, and is additive. The assertion is: if $\varphi\circ f=\psi\circ f$ for every $f$ in the Cartier module of $\Phi$, then $\varphi=\psi$.
--
--   This is the faithfulness half of Cartier's theorem that passage to the Cartier module is a fully faithful functor from commutative formal group laws over a ring of characteristic $p$ to modules over the Cartier ring; the proof cites the surjectivity of the tangent map on Cartier modules and the vanishing of coefficients of indices not divisible by $p$ for a homomorphism with zero linear part. It is used in the Čerednik–Drinfel'd part of the development to turn identities between maps of Cartier modules into identities between homomorphisms of formal $\mathcal{O}_D$-modules, for instance in constructing bases and isogenies of prescribed height.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_eq_of_map_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.eq_of_map_eq
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d d' : ℕ}
    (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f) :
    φ = ψ := by sorry
