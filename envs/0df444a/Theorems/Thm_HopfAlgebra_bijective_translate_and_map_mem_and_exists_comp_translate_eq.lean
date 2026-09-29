-- Prove2me | Theorems.Thm_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq
-- name    : HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/68a10e27-6201-58e3-a632-abc3a7d96dd2
-- title:
--   Translations by points: bijectivity, stability of subalgebras, transitivity
-- statement:
--   Let $k$ be a field and $H$ a commutative ring carrying the structure of a Hopf algebra over $k$, with comultiplication $\Delta =$ `Coalgebra.comul`. Let $\tau$ assign to each $k$-point $g \colon H \to k$ (a $k$-algebra homomorphism) a $k$-algebra endomorphism $\tau g$ of $H$, and assume the compatibility: for every point $g$ and every $h \in H$, the element $\tau g\,(h)$ is obtained from $\Delta h \in H \otimes_k H$ by applying $g \otimes \mathrm{id}_H$ and then the canonical isomorphism $k \otimes_k H \cong H$. Three assertions follow. First, for every point $g$ the map $\tau g$ is bijective. Secondly, if $K$ is a $k$-subalgebra of $H$ such that $\Delta x$ lies in the $k$-span of the set of tensors $a \otimes b$ with $a, b \in K$ for every $x \in K$, then $\tau g\,(x) \in K$ for every point $g$ and every $x \in K$. Thirdly, for any two points $x, y \colon H \to k$ there is a point $g$ with $y = x \circ \tau g$.
--
--   These are the translation (homogeneity) properties of a commutative Hopf algebra acted on by its group of $k$-points: the translations $\tau_g = (g \otimes \mathrm{id}) \circ \Delta$ are automorphisms of the underlying algebra, they preserve any subalgebra whose comultiplication lands in the span of its own tensors, and they act transitively on $k$-points by composition. The result is the input to the faithful flatness statements [`HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed`](thm.html#HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed) and [`HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed`](thm.html#HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed), where the flat locus over a Hopf subalgebra is shown to be stable under all translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (τ : (H →ₐ[k] k) → (H →ₐ[k] H))
    (hτ : ∀ (g : H →ₐ[k] k) (h : H),
      τ g h = Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul h))) :
    (∀ g, Function.Bijective (τ g)) ∧
    (∀ (K : Subalgebra k H),
      (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
      ∀ g, ∀ x ∈ K, τ g x ∈ K) ∧
    (∀ x y : H →ₐ[k] k, ∃ g : H →ₐ[k] k, y = x.comp (τ g)) := by sorry
