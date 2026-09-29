-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt
-- name    : MvFormalGroup.CartierModule.curve_injective_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/a839d302-2ebb-5e47-b7d7-1fff8218ab0f
-- title:
--   Cartier module elements are determined by their curves
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring carrying an algebra structure over $\mathbb{Z}_p$, let $d$ be a natural number, and let $\Phi$ be a $d$-dimensional formal group law over $R$, i.e. a family $(\Phi_i)_{i \in \mathrm{Fin}\,d}$ of multivariate power series in the variables indexed by $\mathrm{Fin}\,d \sqcup \mathrm{Fin}\,d$ with vanishing constant coefficients, with $\Phi_i$ having coefficient $\delta_{ij}$ at each of the two linear monomials $X_{\mathrm{inl}\,j}$ and $X_{\mathrm{inr}\,j}$, and satisfying the associativity identity between the two threefold substitutions; assume moreover that $\Phi$ is commutative in the sense that interchanging the two blocks of variables fixes each $\Phi_i$. Consider the type of elements of the Cartier module of $\Phi$ at $p$: families $(f_j)_{j \in \mathrm{Fin}\,d}$ of power series in variables indexed by $\mathbb{N}$ over $R$, with vanishing constant coefficients, such that for every $j$ the substitution of the Witt addition polynomials $S_n$ for $p$ (the integral Witt addition polynomials pushed forward to $R$, in two blocks of variables indexed by $\{0,1\} \times \mathbb{N}$) into $f_j$ equals $\Phi_j$ evaluated at the two families obtained from $(f_l)_l$ by renaming the variables into the $0$-block and the $1$-block respectively. The assertion is that the map sending such an $f$ to the $d$-tuple of one-variable power series $\bigl(f_j(t,0,0,\dots)\bigr)_{j}$, obtained by substituting the variable $t$ for the $0$-th variable and $0$ for all later variables, is injective.
--
--   This is the uniqueness half of Cartier's theorem that the $p$-typical Witt formal group represents the functor of $p$-typical curves: a homomorphism from the Witt formal group to a commutative formal group law over a $\mathbb{Z}_p$-algebra is determined by the curve it induces. It is used to deduce that the integral Verschiebung on the Cartier module is injective, via [`MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.curve_injective_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Injective
      (MvFormalGroup.CartierModule.curve : MvFormalGroup.CartierModule p Φ → Fin d → PowerSeries R) := by sorry
