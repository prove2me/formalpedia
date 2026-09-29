-- Prove2me | Theorems.Thm_ModularCurve_XOneP_algebraMap_smul_eq_of_isCyclotomicExtension_of_charP
-- name    : ModularCurve.XOneP.algebraMap_smul_eq_of_isCyclotomicExtension_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/3667158a-542b-5a6e-80fd-561831d1b755
-- title:
--   Galois action on A is trivial modulo the maximal ideal
-- statement:
--   Let $p$ be a prime and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for the set $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity. Let $A$ be a discrete valuation domain equipped with an algebra structure over which $L$ is its fraction field, and assume that $p$, viewed in $A$, lies in the maximal ideal of $A$ and that $\zeta$ lies in the image of $A \to L$. Let $k$ be a field of characteristic $p$ carrying an $A$-algebra structure. Assume finally that the group $L \simeq_{\mathbb{Q}} L$ of $\mathbb{Q}$-algebra automorphisms of $L$ acts on $A$ by ring automorphisms (a `MulSemiringAction`), compatibly with the structure map in the sense that $\mathrm{algebraMap}_{A,L}(s \cdot a) = s(\mathrm{algebraMap}_{A,L}(a))$ for all $s$ and all $a \in A$. The conclusion is that for every such automorphism $s$ and every $a \in A$, the images of $s \cdot a$ and of $a$ under the structure map $A \to k$ coincide; that is, $A \to k$ is invariant for this action.
--
--   Since $p$ is totally ramified in $\mathbb{Q}(\zeta_p)$, the residue field of $A$ is $\mathbb{F}_p$ and the Galois group acts trivially on it; this is the arithmetic content of the statement, here in the form that any map from $A$ to a field of characteristic $p$ identifies $s \cdot a$ with $a$. It is used to compare semilinear Galois endomorphisms on $k$-points of a special fibre with the same structure map, in the inertia clause of the special-fibre operator statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_algebraMap_smul_eq_of_isCyclotomicExtension_of_charP.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneP.algebraMap_smul_eq_of_isCyclotomicExtension_of_charP
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a)) :
    ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s • a) = algebraMap A k a := by sorry
