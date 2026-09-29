-- Prove2me | Theorems.Thm_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
-- name    : HopfAlgebra.withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/47fc7b6e-c7b8-5009-a167-86271bdcaf12
-- title:
--   Characters trivial and order prime to char k force φ=ε
-- statement:
--   Let $k$ be an algebraically closed field and let $H$ be a commutative ring carrying a Hopf algebra structure over $k$ whose comultiplication is cocommutative. Write $\mathrm{WithConv}(H \to_{\mathrm{alg}[k]} k)$ for the type of $k$-algebra homomorphisms $H \to k$ equipped with the convolution product, $(\varphi * \psi)(a) = \sum \varphi(a_{(1)})\psi(a_{(2)})$, whose unit $1$ is the counit $\varepsilon$ of $H$; thus, for $G = \operatorname{Spec} H$, this is the commutative monoid $G(k)$ of $k$-points. Let $\varphi$ be such a point, and let $m$ be a natural number whose image in $k$ is nonzero. Assume that $\varphi^m = 1$ for the convolution product, that is, the order of $\varphi$ in $G(k)$ divides $m$, and assume that $\varphi(g) = 1$ for every group-like element $g$ of $H$ over $k$ (an element with $\Delta g = g \otimes g$ which is a unit, equivalently with $\varepsilon(g) = 1$); these are the characters of $G$. The conclusion is that $\varphi = 1$, i.e. $\varphi$ is the counit, the identity element of $G(k)$. No finiteness, flatness or reducedness hypothesis is imposed on $H$.
--
--   This is the unipotent half of the classical count of torsion points of a commutative affine group scheme over an algebraically closed field: the common kernel of all characters contains no nontrivial rational point of finite order prime to the characteristic. It is used in bounding the number of torsion points for the relative group law in the affine case, in [`GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine`](thm.html#GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem HopfAlgebra.withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
    (k : Type u) [Field k] [IsAlgClosed k] (H : Type v) [CommRing H] [HopfAlgebra k H]
    [Coalgebra.IsCocomm k H]
    (φ : WithConv (H →ₐ[k] k)) (m : ℕ) (hm : (m : k) ≠ 0) (hφ : φ ^ m = 1)
    (h1 : ∀ g : H, IsGroupLikeElem k g → φ g = 1) :
    φ = 1 := by sorry
