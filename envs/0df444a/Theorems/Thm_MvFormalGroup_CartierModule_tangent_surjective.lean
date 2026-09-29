-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
-- name    : MvFormalGroup.CartierModule.tangent_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/d7e87fa4-dda4-56c6-bc78-d8a53bf0298b
-- title:
--   Surjectivity of the tangent map of a Cartier module
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring of characteristic $p$, let $d$ be a natural number, and let $\Phi$ be a $d$-dimensional formal group law over $R$: a $d$-tuple of multivariate power series $\Phi_i$ in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with zero constant coefficient, whose linear coefficients in the left- and right-hand blocks are both given by the identity matrix, and which satisfies the associativity identity between the two threefold substitutions. Assume $\Phi$ is commutative in the sense of [`MvFormalGroup.IsComm`](def/MvFormalGroup_BasicV2.html#L52), i.e. interchanging the two blocks of variables fixes each $\Phi_i$. The Cartier module [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) consists of the $d$-tuples $f = (f_j)_{j}$ of power series in variables indexed by $\mathbb{N}$ over $R$ with zero constant coefficients such that, for every $j$, substituting the family `WittLaw.addFam p R` of $p$-typical Witt addition polynomials (reduced from $\mathbb{Z}$ to $R$) into $f_j$ agrees with substituting into $\Phi_j$ the pair consisting of $f$ with its variables renamed to the first and to the second copy of $\mathbb{N}$. The map [`MvFormalGroup.CartierModule.tangent`](def/MvFormalGroup_CartierModule.html#L1037) sends such an $f$ to the vector of coefficients of the first variable $X_0$ in the $f_j$, and is an additive homomorphism to $\mathrm{Fin}\,d \to R$. The assertion is that this map is surjective: every vector in $R^d$ arises as the tangent vector of some element of the Cartier module of $\Phi$.
--
--   This is the existence half of Cartier's structure theorem for the module of $p$-typical curves of a commutative formal group law in characteristic $p$, the surjectivity of $\mathrm{Hom}(\widehat{W},\Phi) \to \operatorname{Lie}\Phi$; the complementary statement identifies the kernel with $V$ times the module. It is used to produce Cartier-module elements with prescribed tangent vectors, for instance in [`MvFormalGroup.CartierModule.eq_of_map_eq`](thm.html#MvFormalGroup.CartierModule.eq_of_map_eq) and in the analysis of graded pieces of formal modules over quaternionic data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_tangent_surjective.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.tangent_surjective
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
      (MvFormalGroup.CartierModule.tangent : MvFormalGroup.CartierModule p Φ → Fin d → R) := by sorry
