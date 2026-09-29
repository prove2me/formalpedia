-- Prove2me | Theorems.Thm_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker
-- name    : Module.finrank_iInf_ker_baseChange_eq_finrank_iInf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/7842502a-9f11-52c4-b25f-9c70ad6bad8a
-- title:
--   Joint kernel dimension is invariant under field extension
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, let $V$ be an $F$-vector space that is finite as an $F$-module, and let $\iota$ be an arbitrary type (possibly empty or infinite) indexing a family $T : \iota \to (V \to_{F} V)$ of $F$-linear endomorphisms of $V$. For each $i$, let $(T_i)_{K}$ denote the $K$-linear endomorphism of $K \otimes_F V$ obtained from $T_i$ by base change along $F \to K$. The assertion is the equality of finite ranks
--   $$\operatorname{finrank}_K\Bigl(\bigcap_{i \in \iota} \ker\bigl((T_i)_K\bigr)\Bigr) = \operatorname{finrank}_F\Bigl(\bigcap_{i \in \iota} \ker T_i\Bigr),$$
--   where on each side the intersection is the infimum, in the lattice of submodules of $K \otimes_F V$ respectively of $V$, of the kernels of the members of the family, regarded as a module over $K$ respectively $F$, and $\operatorname{finrank}$ is the natural-number rank (the empty intersection convention gives the whole space when $\iota$ is empty).
--
--   This is the standard fact that the dimension of the solution space of a system of linear conditions on a finite-dimensional vector space is unchanged by extension of the scalar field, here in the form of an arbitrary family of endomorphisms and their joint kernel. It is used as a linear-algebra input in [`ModularCurve.natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient`](thm.html#ModularCurve.natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem Module.finrank_iInf_ker_baseChange_eq_finrank_iInf_ker
    (F : Type) [Field F] (K : Type) [Field K] [Algebra F K]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
    {ι : Type} (T : ι → (V →ₗ[F] V)) :
    Module.finrank K ↥(⨅ i, LinearMap.ker ((T i).baseChange K)) =
      Module.finrank F ↥(⨅ i, LinearMap.ker (T i)) := by sorry
