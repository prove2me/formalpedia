-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
-- name    : Module.FaithfullyFlat.exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/d8eee577-67ac-56ba-8dc5-812d2c6f47e6
-- title:
--   Split twisted forms of ℤ^G over ℤ are coboundaries
-- statement:
--   Let $A$ be a commutative ring which is faithfully flat as a $\mathbb{Z}$-module, let $G$ be a finite additive abelian group, and let $e : G \to A \otimes_{\mathbb{Z}} A$ be a family forming a complete system of orthogonal idempotents of $A \otimes_{\mathbb{Z}} A$, i.e. each $e(g)$ is idempotent, $e(g)e(h) = 0$ for $g \neq h$, and $\sum_{g} e(g) = 1$. Let $M$ be a $\mathbb{Z}$-submodule of the functions $G \to A$ whose membership is given by the twisted descent condition: $f \in M$ if and only if $\sum_{m \in G} e(m)\,(f(k-m) \otimes 1) = 1 \otimes f(k)$ for every $k \in G$. Assume further that the inclusion $M \hookrightarrow (G \to A)$ exhibits $G \to A$ as the base change of $M$ along $\mathbb{Z} \to A$, that is, the induced $A$-linear map $A \otimes_{\mathbb{Z}} M \to (G \to A)$ is an isomorphism. The conclusion is that $e$ is a coboundary: there exists $d : G \to A$ which is a complete system of orthogonal idempotents of $A$ such that $e(k) = \sum_{i \in G} d(i) \otimes d(i-k)$ for all $k \in G$.
--
--   This is the vanishing of the Čech $H^1$ of $\operatorname{Spec}\mathbb{Z}$ with coefficients in a finite constant abelian group, in idempotent form: a twisted form of the trivial $G$-torsor over $A$ that becomes split after base change is already a coboundary. The submodule $M$ is, under these hypotheses, a nonzero finite étale $\mathbb{Z}$-algebra, and the proof invokes [`Algebra.FormallyUnramified.nonempty_ringHom_int`](thm.html#Algebra.FormallyUnramified.nonempty_ringHom_int) (Minkowski: such an algebra admits a ring homomorphism to $\mathbb{Z}$) to produce the idempotents $d$; it feeds the descent criterion [`Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary`](thm.html#Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Module.FaithfullyFlat.exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
    (A : Type u) [CommRing A] [Module.FaithfullyFlat ℤ A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[ℤ] A) (he : CompleteOrthogonalIdempotents e)
    (M : Submodule ℤ (G → A))
    (hM : ∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] f k)
    (hbc : IsBaseChange A M.subtype) :
    ∃ d : G → A, CompleteOrthogonalIdempotents d ∧ ∀ k, e k = ∑ i, d i ⊗ₜ[ℤ] d (i - k) := by sorry
