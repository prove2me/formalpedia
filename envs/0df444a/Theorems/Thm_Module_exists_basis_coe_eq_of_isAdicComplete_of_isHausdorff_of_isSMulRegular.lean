-- Prove2me | Theorems.Thm_Module_exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular
-- name    : Module.exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/19d26779-31eb-5e5c-a8bb-6d8d259bd420
-- title:
--   Lifting a basis of M/π M to a basis of M
-- statement:
--   Let $A$ be a commutative ring and $\pi \in A$ an element for which $A$ is adically complete for the ideal $(\pi) =$ `Ideal.span {π}`, i.e. separated and complete in the sense of Mathlib's `IsAdicComplete`. Let $M$ be an $A$-module (an additive commutative group with an $A$-action) which is Hausdorff for the $(\pi)$-adic filtration, $\bigcap_n (\pi)^n \cdot M = 0$, and on which multiplication by $\pi$ is injective ($\pi$ acts as a regular element, `IsSMulRegular M π`). Let $\iota$ be a finite index set, and let $b$ be a basis of $M/((\pi)\cdot M)$, the quotient of $M$ by the submodule $(\pi)\cdot\top$, as a module over $A/(\pi)$. Let $e : \iota \to M$ be a family of elements of $M$ whose images under the quotient map $M \to M/((\pi)\cdot M)$ are the basis vectors, $\overline{e_i} = b_i$ for every $i$. The conclusion is that there exists an $A$-basis $b'$ of $M$ indexed by $\iota$ whose underlying family of vectors is exactly $e$; in particular $M$ is free of rank $|\iota|$ over $A$.
--
--   This is the standard freeness criterion over a $\pi$-adically complete base: any lift of a basis of $M/\pi M$ is a basis of $M$, provided $\pi$ acts injectively on $M$ and $M$ is $\pi$-adically separated. It is used to show that a Cartier module of finite height is free of the expected rank, via [`MvFormalGroup.CartierModule.nonempty_basis_of_finrank_eq_pow`](thm.html#MvFormalGroup.CartierModule.nonempty_basis_of_finrank_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Module.exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular
    {A : Type u} [CommRing A] (π : A) [IsAdicComplete (Ideal.span {π}) A]
    {M : Type v} [AddCommGroup M] [Module A M] [IsHausdorff (Ideal.span {π}) M]
    (hπ : IsSMulRegular M π) {ι : Type w} [Finite ι]
    (b : Module.Basis ι (A ⧸ Ideal.span {π}) (M ⧸ (Ideal.span {π} • ⊤ : Submodule A M)))
    (e : ι → M) (he : ∀ i, Submodule.Quotient.mk (e i) = b i) :
    ∃ b' : Module.Basis ι A M, ⇑b' = e := by sorry
