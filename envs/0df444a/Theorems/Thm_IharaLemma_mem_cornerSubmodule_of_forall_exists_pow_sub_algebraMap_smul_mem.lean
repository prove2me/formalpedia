-- Prove2me | Theorems.Thm_IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem
-- name    : IharaLemma.mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/1e6453c6-19d2-5ad3-a253-8bd6863eacb6
-- title:
--   Fullness of a corner under adic generalised eigenvector conditions
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring, $B$ a commutative $\mathcal{O}$-algebra, and $V$ an abelian group carrying compatible $\mathcal{O}$- and $B$-module structures (a scalar tower). Assume $V$ is separated for the maximal-ideal-adic filtration: any $v \in V$ lying in the submodule $\mathfrak{m}_{\mathcal{O}}^{k} \cdot V$ for every $k \in \mathbb{N}$, where $\mathfrak{m}_{\mathcal{O}}$ is the maximal ideal of $\mathcal{O}$, is zero. Let $S$ be an idempotent splitting of $B$: a natural number $n$, elements $e_0,\dots,e_{n-1} \in B$ forming a complete family of orthogonal idempotents, and ideals $\mathfrak{m}_0,\dots,\mathfrak{m}_{n-1}$ of $B$, each maximal, such that every maximal ideal of $B$ equals some $\mathfrak{m}_j$, and $e_j \in \mathfrak{m}_l$ if and only if $j \neq l$. Fix an index $i$, a subset $G \subseteq B$ generating $B$ as an $\mathcal{O}$-algebra ($\mathrm{adjoin}_{\mathcal{O}} G = B$), and a function $c \colon B \to \mathcal{O}$ with $g - c(g) \in \mathfrak{m}_i$ for all $g \in G$ (the image of $c(g)$ under the structure map being understood). Suppose $v \in V$ satisfies: for every $g \in G$ and every $k \in \mathbb{N}$ there is $n \in \mathbb{N}$ with $(g - c(g))^{n} \cdot v \in \mathfrak{m}_{\mathcal{O}}^{k} \cdot V$. Then $v$ lies in the image of the $B$-linear map $w \mapsto e_i \cdot w$ on $V$, i.e. $v = e_i w$ for some $w \in V$.
--
--   This is the fullness half of the description of the $i$-th corner $e_i V$ of a module over a semilocal algebra $B$ with a complete orthogonal idempotent splitting: a vector on which each algebra generator acts, adically, like the scalar $c(g)$ attached to the maximal ideal $\mathfrak{m}_i$ must already lie in that corner. It is used in the construction and comparison of corner data for cohomological Hecke modules, in particular in the statements producing corners at auxiliary levels and refinements of corner families.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Maps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing IharaLemma

theorem IharaLemma.mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    (hsep : ∀ v : V, (∀ k : ℕ, v ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) → v = 0)
    (S : IdempotentSplitting B) (i : Fin S.n)
    (G : Set B) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (c : B → 𝒪) (hc : ∀ g ∈ G, g - algebraMap 𝒪 B (c g) ∈ S.𝔪 i)
    (v : V)
    (hv : ∀ g ∈ G, ∀ k : ℕ, ∃ n : ℕ,
      ((g - algebraMap 𝒪 B (c g)) ^ n) • v ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) :
    v ∈ cornerSubmodule (M := V) (S.e i) := by sorry
