-- Prove2me | Theorems.Thm_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset
-- name    : Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/fdf9f445-fa4c-57eb-be38-b34f33db4ae3
-- title:
--   Grassmannian charts are open subfunctors
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module, $k$ a natural number and $x : \mathrm{Fin}\,k \to M$ a $k$-tuple of elements of $M$. Let $A$ be a commutative $R$-algebra and let $N$ be an element of `Module.Grassmannian A (A ⊗[R] M) k`, that is, an $A$-submodule of $A \otimes_R M$ whose quotient is projective of rank $k$. The assertion is that there exists a subset $U$ of $\operatorname{Spec} A$ which is open and has the following property: for every commutative $R$-algebra $B$ and every $R$-algebra homomorphism $\varphi : A \to B$, the $B$-linear map
--   $$B^k \longrightarrow (B \otimes_R M)/\,\mathrm{map}\,\varphi\,N, \qquad v \longmapsto \sum_{i} v_i \cdot \overline{1 \otimes x_i},$$
--   where $\mathrm{map}\,\varphi\,N$ denotes the base change `Module.Grassmannian.map φ N` of $N$ along $\varphi$ and the bar denotes the canonical projection to the quotient, is bijective if and only if the image of the induced map $\operatorname{Spec} B \to \operatorname{Spec} A$, `PrimeSpectrum.comap φ.toRingHom`, is contained in $U$. The open set $U$ is produced uniformly in $B$ and $\varphi$, i.e. a single $U$ tests the condition for all base changes simultaneously.
--
--   This is the statement that the standard chart of the Grassmannian functor attached to a tuple $x_1,\dots,x_k$ of elements of $M$ — the locus where the classes of $1 \otimes x_i$ freely generate the rank-$k$ quotient — is an open subfunctor, the pullback of the chart along an $A$-point being the open subscheme $U$ of $\operatorname{Spec} A$. It is the input needed to glue the charts into a scheme, and is used by [`Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover`](thm.html#Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M)
    (A : Type) [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        (Function.Bijective fun v : Fin k → B =>
            ∑ i, v i • (Module.Grassmannian.map φ N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) ↔
          Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U := by sorry
