-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing
-- name    : MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/dcdc3ad3-0007-519d-811e-f4b6da7d43b3
-- title:
--   Fullness of the Cartier module functor over a perfect field
-- statement:
--   Fix a prime $p$ and a perfect field $k$ of characteristic $p$, and let $\Phi$, $\Phi'$ be commutative formal group laws over $k$ of dimensions $d$ and $d'$: that is, $\Phi$ is a $d$-tuple of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with zero constant term, linear part the identity in each block, satisfying associativity, together with the symmetry condition `IsComm` that interchanging the two blocks of variables fixes each component, and likewise for $\Phi'$. The Cartier module `CartierModule p Φ` consists of the $d$-tuples $f$ of power series in variables indexed by $\mathbb{N}$, with zero constant term, satisfying $f \circ (\text{Witt addition polynomials}) = \Phi(f(X), f(Y))$; it carries the additive operators `frobenius`, `verschiebung` and, for each $a \in k$, `homothety a`, given by precomposing $f$ with the Verschiebung, Frobenius and Teichmüller endomorphisms of the Witt formal group. Let $\theta$ be an additive map from `CartierModule p Φ` to `CartierModule p Φ'` commuting with `frobenius`, with `verschiebung`, and with `homothety a` for every $a \in k$. Then there is a homomorphism $\varphi \colon \Phi \to \Phi'$ of formal group laws — a $d'$-tuple of power series in $d$ variables without constant term satisfying $\varphi \circ \Phi = \Phi' (\varphi, \varphi)$ — such that $\theta(f)$ equals the Cartier-module map induced by $\varphi$, namely $\varphi \circ f$, for every $f$.
--
--   This is the fullness half of Cartier's equivalence between commutative formal group laws over a perfect field of characteristic $p$ and modules over the Cartier ring $\mathrm{Cart}_p(k)$: the hypotheses on $\theta$ say precisely that it is $\mathrm{Cart}_p(k)$-linear, and the conclusion produces a homomorphism of laws inducing it. It is used in the study of special formal $\mathcal{O}_D$-modules in the Čerednik–Drinfel'd setting, where isogenies and isomorphisms of formal modules are constructed from maps of their Cartier modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d d' : ℕ}
    (Φ : MvFormalGroup d k) (Φ' : MvFormalGroup d' k) [Φ.IsComm] [Φ'.IsComm]
    (θ : MvFormalGroup.CartierModule p Φ →+ MvFormalGroup.CartierModule p Φ')
    (hF : ∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
      MvFormalGroup.CartierModule.frobenius (θ f))
    (hV : ∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) =
      MvFormalGroup.CartierModule.verschiebung (θ f))
    (hH : ∀ (a : k) f, θ (MvFormalGroup.CartierModule.homothety a f) =
      MvFormalGroup.CartierModule.homothety a (θ f)) :
    ∃ φ : Φ.Hom Φ', ∀ f, MvFormalGroup.CartierModule.map φ f = θ f := by sorry
