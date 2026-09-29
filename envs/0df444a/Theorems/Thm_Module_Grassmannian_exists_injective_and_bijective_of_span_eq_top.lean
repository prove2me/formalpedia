-- Prove2me | Theorems.Thm_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top
-- name    : Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/ae72fdcd-4447-580b-a306-4bc8b5b23bc1
-- title:
--   Standard charts from a generating family cover field-valued Grassmannian points
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module, $k$ a natural number, $\iota$ a type and $g : \iota \to M$ a family whose $R$-span is all of $M$, i.e. $\mathrm{span}_R(\mathrm{range}\,g) = \top$. Let $K$ be a field carrying an $R$-algebra structure, and let $N$ be a point of `Module.Grassmannian K (K ⊗[R] M) k`, that is a $K$-submodule $N = N.\mathrm{toSubmodule}$ of $K \otimes_R M$ whose quotient $(K \otimes_R M)/N$ is finitely generated projective of rank $k$ at every stalk. The assertion is that there exists a map $I : \mathrm{Fin}\,k \to \iota$ which is injective and for which the $K$-linear map
--   $$K^k \longrightarrow (K \otimes_R M)/N, \qquad v \longmapsto \sum_{i} v_i \cdot \overline{1 \otimes g(I(i))},$$
--   written using the quotient map `N.toSubmodule.mkQ`, is bijective; here $\overline{\,\cdot\,}$ denotes the class modulo $N$ of the element $1 \otimes_R g(I(i))$ of $K \otimes_R M$. In other words, $N$ lies in the standard chart attached to the $k$-tuple $(g_{I(0)},\dots,g_{I(k-1)})$ of members of the generating family.
--
--   This is the statement that, for field-valued points, the standard charts of the Grassmannian functor indexed by injective $k$-element subfamilies of a fixed generating family of $M$ are jointly surjective. It is used in the construction of the Grassmannian as a scheme, in [`Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents`](thm.html#Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents) and in [`Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover`](thm.html#Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover), where it supplies the covering family of affine charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (K : Type) [Field K] [Algebra R K] (N : Module.Grassmannian K (K ⊗[R] M) k) :
    ∃ I : Fin k → ι, Function.Injective I ∧
      Function.Bijective fun v : Fin k → K =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : K) ⊗ₜ[R] g (I i)) := by sorry
