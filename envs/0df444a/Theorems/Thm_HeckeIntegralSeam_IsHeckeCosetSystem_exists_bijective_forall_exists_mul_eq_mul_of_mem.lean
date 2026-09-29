-- Prove2me | Theorems.Thm_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem
-- name    : HeckeIntegralSeam.IsHeckeCosetSystem.exists_bijective_forall_exists_mul_eq_mul_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/ea0fe83f-991c-5be1-8c1f-1d0e9d33a125
-- title:
--   Left multiplication by u ∈ U permutes a Hecke coset system
-- statement:
--   Let $G$ be a group, $U \le G$ a subgroup, $g \in G$, and let $\mathrm{reps} \colon \iota_0 \to G$ be a family indexed by an arbitrary type $\iota_0$ which is a Hecke coset system for $(U,g)$ in the sense of `IsHeckeCosetSystem`: each $\mathrm{reps}\,i$ lies in the double coset $U\{g\}U = (U : \mathrm{Set}\,G) \cdot \{g\} \cdot (U : \mathrm{Set}\,G)$; every $x$ in that double coset satisfies $xU = (\mathrm{reps}\,i)U$ in $G \mathbin{/} U$ for some $i$; and the map $i \mapsto (\mathrm{reps}\,i)U \in G \mathbin{/} U$ is injective. Let $u \in G$ with $u \in U$. The conclusion asserts the existence of a map $\pi \colon \iota_0 \to \iota_0$ which is bijective and such that for every $i \in \iota_0$ there is some $u' \in U$ with $u \cdot \mathrm{reps}\,i = \mathrm{reps}\,(\pi\,i) \cdot u'$; equivalently, left translation by $u$ sends the coset $(\mathrm{reps}\,i)U$ to $(\mathrm{reps}\,(\pi\,i))U$. No finiteness of the index type is assumed.
--
--   This is the elementary permutation lemma underlying the theory of Hecke operators for a pair $(G,U)$: left multiplication by an element of $U$ maps the double coset $UgU$ onto itself and thus permutes the left $U$-cosets into which it decomposes. It is used in this development to establish the $U$-invariance of sums of the form $x \mapsto \sum_i f(x \cdot \mathrm{reps}\,i)$, and is cited by [`AutomorphicForm.isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem`](thm.html#AutomorphicForm.isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.lean

import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeIntegralSeam.IsHeckeCosetSystem.exists_bijective_forall_exists_mul_eq_mul_of_mem
    {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι₀ : Type*} {reps : ι₀ → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (u : G) (hu : u ∈ U) :
    ∃ π : ι₀ → ι₀, Function.Bijective π ∧
      ∀ i : ι₀, ∃ u' ∈ U, u * reps i = reps (π i) * u' := by sorry
