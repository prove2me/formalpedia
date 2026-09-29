-- Prove2me | Theorems.Thm_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
-- name    : IharaLemma.map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/357bf1a6-6480-5475-a0f4-8a9f10e5d97d
-- title:
--   Corner transport along an 𝒪-linear intertwining map
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring, let $B$ and $B'$ be commutative $\mathcal{O}$-algebras that are finite as $\mathcal{O}$-modules, and let $V$, $V'$ be abelian groups carrying compatible $\mathcal{O}$- and $B$- (resp. $B'$-) module structures, the $B$- and $B'$-actions extending the $\mathcal{O}$-actions. Let $f\colon V\to V'$ be $\mathcal{O}$-linear. Let $S$ be an idempotent splitting of $B$, that is, data consisting of a natural number $n$, elements $e_j\in B$ forming a complete orthogonal family of idempotents, and maximal ideals $\mathfrak m_j$ of $B$ ($j\in\mathrm{Fin}\,n$) exhausting all maximal ideals of $B$ and satisfying $e_j\in\mathfrak m_k\iff j\neq k$; fix an index $i$. Let $S'$ be such a splitting of $B'$, with data $e'_{j'},\mathfrak m'_{j'}$, and fix $i'$. Assume: (i) $V'$ is separated for the $\mathfrak m_{\mathcal O}$-adic filtration, i.e. any $v'\in V'$ lying in $\mathfrak m_{\mathcal O}^{k}\cdot V'$ for every $k$ is $0$; (ii) $G'\subseteq B'$ generates $B'$ as an $\mathcal{O}$-algebra, $\mathrm{adjoin}_{\mathcal O}(G')=\top$; (iii) every $g'\in G'$ admits $c\in\mathcal{O}$ and $g_0\in B$ with $g'-c\in\mathfrak m'_{i'}$, $g_0-c\in\mathfrak m_i$, and $f(g_0\cdot v)=g'\cdot f(v)$ for all $v\in V$. Then $f$ carries the corner $e_i\cdot V$ (the range of multiplication by $e_i$ on $V$) into the corner $e'_{i'}\cdot V'$: every $w$ in the former has $f(w)$ in the latter.
--
--   This is the transport step for local components in the Ihara-lemma package: it says that an intertwining $\mathcal{O}$-linear map between two modules, over finite $\mathcal{O}$-algebras split into local corners, respects the chosen corners as soon as the algebra generators at the target level are residually scalar at $\mathfrak m'_{i'}$ and have residually equal partners at $\mathfrak m_i$. It is used to compare local components of degeneracy maps between cohomology at two levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner.lean

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Definitions.Def_IharaLemma_IdempotentSplitting

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    [Module.Finite 𝒪 B] [Module.Finite 𝒪 B']
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V →ₗ[𝒪] V') (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    (S' : IharaLemma.IdempotentSplitting B') (i' : Fin S'.n)
    (hsep : ∀ v' : V', (∀ k : ℕ, v' ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V')) → v' = 0)
    (G' : Set B') (hG' : Algebra.adjoin 𝒪 G' = ⊤)
    (hgen : ∀ g' ∈ G', ∃ (c : 𝒪) (g₀ : B), g' - algebraMap 𝒪 B' c ∈ S'.𝔪 i' ∧
      g₀ - algebraMap 𝒪 B c ∈ S.𝔪 i ∧ ∀ v : V, f (g₀ • v) = g' • f v) :
    ∀ w ∈ IharaLemma.cornerSubmodule (M := V) (S.e i),
      f w ∈ IharaLemma.cornerSubmodule (M := V') (S'.e i') := by sorry
