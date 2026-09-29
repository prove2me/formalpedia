-- Prove2me | Theorems.Thm_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension
-- name    : Module.ker_baseChange_le_range_and_finrank_eq_of_field_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b64597c4-c39b-5148-88af-8348ed74b839
-- title:
--   Descent of exactness and ker dimension along K ⊆ K'
-- statement:
--   Let $R$ be a commutative ring, let $C : \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules equipped with $R$-linear maps $d_i : C_i \to C_{i+1}$, and let $\Theta : F \to C_0$ be an $R$-linear map from an $R$-module $F$. Let $K$ and $K'$ be fields that are $R$-algebras, with $K'$ a $K$-algebra in such a way that $R \to K \to K'$ is a scalar tower, and let $r$ be a natural number. Assume three conditions after base change to $K'$: for every $i$, the kernel of $d_{i+1} \otimes K'$ is contained in the image of $d_i \otimes K'$; the kernel of $d_0 \otimes K'$ is contained in the image of $\Theta \otimes K'$; and the $K'$-dimension of $\ker(d_0 \otimes K')$ equals $r$. The conclusion is the conjunction of the three corresponding statements over $K$: for every $i$, $\ker(d_{i+1} \otimes K) \subseteq \operatorname{im}(d_i \otimes K)$; $\ker(d_0 \otimes K) \subseteq \operatorname{im}(\Theta \otimes K)$; and $\dim_K \ker(d_0 \otimes K) = r$. Here $\otimes K$ denotes `LinearMap.baseChange`, i.e. the map induced on $K \otimes_R -$, and the dimension is `Module.finrank` (so the equality with $r$ also covers the convention that infinite-dimensional spaces have `finrank` $0$).
--
--   This is the module-level form of descent of exactness along a field extension: exactness of a base-changed complex in positive degrees, surjectivity onto the degree-zero cohomology from $F$, and the dimension of the degree-zero kernel all descend from $K'$ to a subfield $K$ over which the complex is already defined by base change from $R$. It is used in the construction of points of the Hilbert functor, in [`AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation), where a cohomological computation available over a large field must be transported back to a smaller one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.ker_baseChange_le_range_and_finrank_eq_of_field_extension
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1))
    {F : Type u} [AddCommGroup F] [Module R F] (Θ : F →ₗ[R] C 0)
    (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R K K'] (r : ℕ)
    (h1 : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K') ≤ LinearMap.range ((d i).baseChange K'))
    (h2 : LinearMap.ker ((d 0).baseChange K') ≤ LinearMap.range (Θ.baseChange K'))
    (h3 : Module.finrank K' (LinearMap.ker ((d 0).baseChange K')) = r) :
    (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) ∧
    LinearMap.ker ((d 0).baseChange K) ≤ LinearMap.range (Θ.baseChange K) ∧
    Module.finrank K (LinearMap.ker ((d 0).baseChange K)) = r := by sorry
