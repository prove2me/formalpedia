-- Prove2me | Theorems.Thm_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul
-- name    : IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/393c9b3a-2ca2-535b-b662-5f9d7fdf1c8a
-- title:
--   Elements of mathfrak mᵢ are topologically nilpotent on the eᵢ-corner
-- statement:
--   Let $\mathcal O$ be a commutative local ring and $B$ a commutative $\mathcal O$-algebra which is finite as an $\mathcal O$-module. Let $S$ be an idempotent splitting of $B$: an integer $n_S$, elements $e_0,\dots,e_{n_S-1}$ of $B$ forming a complete orthogonal family of idempotents, and ideals $\mathfrak m_0,\dots,\mathfrak m_{n_S-1}$ of $B$, each maximal, such that every maximal ideal of $B$ is one of the $\mathfrak m_j$, and $e_j \in \mathfrak m_l$ if and only if $j \neq l$. Fix an index $i$ and an element $b \in \mathfrak m_i$, a module $V$ carrying compatible $\mathcal O$- and $B$-module structures (the $\mathcal O$-action being the restriction of the $B$-action along $\mathcal O \to B$), and a natural number $k$. Then there exists $n \in \mathbb N$ such that for every $v$ in the corner submodule $e_i \cdot V$, that is the range of the $B$-linear map $V \to V$, $m \mapsto e_i \cdot m$, one has $b^n \cdot v \in \mathfrak m_{\mathcal O}^k \cdot V$, where $\mathfrak m_{\mathcal O}$ is the maximal ideal of $\mathcal O$ and $\mathfrak m_{\mathcal O}^k \cdot V$ denotes the $\mathcal O$-submodule $\mathfrak m_{\mathcal O}^k \cdot \top$ of $V$. As stated, the exponent $n$ is allowed to depend on $V$ as well as on $S$, $i$, $b$ and $k$.
--
--   This is the topological-nilpotence input used when transporting statements between the corners of a Hecke algebra that has been split by the complete orthogonal idempotents attached to its maximal ideals: an element of the maximal ideal $\mathfrak m_i$ (in practice a Hecke operator minus its residual eigenvalue) becomes nilpotent modulo any fixed power of $\mathfrak m_{\mathcal O}$ when acting on the $i$-th corner. It is invoked by the corner-transport lemmas for the cohomology carriers appearing in the Ihara-type argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul.lean

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Definitions.Def_IharaLemma_IdempotentSplitting

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    (S : IdempotentSplitting B) (i : Fin S.n) (b : B) (hb : b ∈ S.𝔪 i)
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V] (k : ℕ) :
    ∃ n : ℕ, ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) →
      (b ^ n) • v ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by sorry
