-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebungInt_eq
-- name    : MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebungInt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/fe504c1e-0d00-55ad-8a99-4a1dbc044408
-- title:
--   V-reducedness of the Cartier module over a ℤₚ-algebra
-- statement:
--   Fix a prime $p$ and a commutative ring $R$ carrying a $\mathbb{Z}_p$-algebra structure, and let $\Phi$ be a $d$-dimensional formal group law over $R$, that is, a $d$-tuple of power series in the $2d$ variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant terms, linear coefficients $\delta_{ij}$ in each of the two blocks of variables, and satisfying the associativity identity, which is assumed commutative in the sense that interchanging the two blocks of variables fixes each component. Let $f$ be an element of the Cartier module [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162): a $d$-tuple of power series in the variables $x_0,x_1,\dots$ indexed by $\mathbb{N}$ over $R$, each with zero constant coefficient, such that substituting the Witt addition polynomials $S_n$ (the images in $R$ of `WittVector.wittAdd p n`) into $f$ equals $\Phi$ evaluated at the two copies of $f$ in the separate variable families. Then the tangent vector of $f$, namely the $d$-tuple of coefficients of the monomial $x_0$ in the components of $f$, vanishes if and only if $f$ lies in the image of the integral Verschiebung `verschiebungInt`, the additive endomorphism given by substituting the integral Frobenius family of the Witt formal group into a Cartier module element; that is, $f = Vg$ for some $g$ in the same Cartier module.
--
--   This is Cartier's statement that the module of $p$-typical curves of a commutative formal group law over a $\mathbb{Z}_p$-algebra is $V$-reduced, with $M/VM$ identified with the tangent space: an element has zero tangent vector exactly when it is divisible by the Verschiebung. It is used in the base-change surjectivity statement for Cartier modules and, further on, in the study of the formal modules attached to special formal $\mathcal{O}_D$-modules in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebungInt_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebungInt_eq
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (f : MvFormalGroup.CartierModule p Φ) :
    MvFormalGroup.CartierModule.tangent f = 0 ↔
      ∃ g : MvFormalGroup.CartierModule p Φ, MvFormalGroup.CartierModule.verschiebungInt g = f := by sorry
