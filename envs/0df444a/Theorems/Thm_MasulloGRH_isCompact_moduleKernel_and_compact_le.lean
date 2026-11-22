-- Prove2me | Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le
-- name    : MasulloGRH.isCompact_moduleKernel_and_compact_le
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:04:12.458103+00:00
-- url     : https://prove2.me/theorems/1018a9e2-5428-47e0-9da1-aa88c1128563
-- title:
--   The kernel $G^1$ of a module is compact and contains every compact subgroup
-- statement:
--   Let $(G,|\cdot|_G)$ be an $\mathbb R_{>0}$-modulated abelian topological group, i.e. $|\cdot|_G\colon G\to\mathbb R_{>0}$ is a continuous proper non-trivial surjective homomorphism. Let
--   $$G^1=\{g\in G:\ |g|_G=1\}$$
--   be its kernel. Then:
--   - $G^1$ is compact;
--   - every compact subgroup $k\subseteq G$ is contained in $G^1$.
--
--   The second statement holds because $\mathbb R_{>0}$ has no non-trivial compact subgroups. In Masullo's §D.3.3 these two facts give the decomposition $G\simeq\mathbb R_{>0}\times G^1$. They also show that the good subgroups $k$ that define the stages $\mathcal S_I(k,G)$ of $\mathcal S_I(G)$ all lie in the compact group $G^1$. Hence each $G/k\simeq\mathbb R\times G^1/k$ is an elementary group.
--
--   **Formalization Note.** $G^1$ is given as a subgroup of $G$ whose elements are exactly those of module $1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3, opening paragraphs (p. 804)

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

namespace MasulloGRH

theorem isCompact_moduleKernel_and_compact_le (G : Type*) [CommGroup G] [TopologicalSpace G]
    (m : G → ℝ) (hm : IsRposModule m) (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1) :
    IsCompact (G1 : Set G) ∧ ∀ k : Subgroup G, IsCompact (k : Set G) → k ≤ G1 := by
  sorry

end MasulloGRH
