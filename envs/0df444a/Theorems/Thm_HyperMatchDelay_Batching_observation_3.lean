-- Prove2me | Theorems.Thm_HyperMatchDelay_Batching_observation_3
-- name    : HyperMatchDelay.Batching.observation_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:00.27256+00:00
-- url     : https://prove2.me/theorems/bb6af53a-f3dd-44cb-a3f7-f0556e6980ea
-- title:
--   Observation 3, p. 19 — a long edge of a batch meets its first k and its last k vertices
-- statement:
--   Let $d, k, n$ be natural numbers, $z \in \mathbb N$, $i \in \mathbb Z$, and let $B = V_{z,i} = \{v \in [n] : z + id \le v \le z + (i+1)d - 1\}$ be a batch window. Let $L$ be the $k$ smallest and $R$ the $k$ largest elements of $B$ (all of $B$ if $|B| \le k$). If $e \subseteq B$ is a non-empty hyperedge with
--   $$ \mathrm{diam}(e) > d - k, $$
--   then $e \cap L \neq \emptyset$ and $e \cap R \neq \emptyset$.
--
--   Equivalently, an edge of the batch that misses $L$ or misses $R$ has diameter at most $d - k$, so it is a short edge. Hence the long edges of any matching restricted to a batch form a restricted matching in $\mathcal M_{L,R}$, which Depth-k Greedy enumerates.
--
--   **Formalization Note** The paper assumes without loss of generality $V_{z,i} = \{0, \dots, d-1\}$; here the window may be truncated at $1$ or $n$, and $L$, $R$ are the first and last $k$ elements of the truncated window. The comparison $\mathrm{diam}(e) > d - k$ is made in $\mathbb Z$, so for $d < k$ every non-empty edge counts as long. The paper states the observation for edges of $M^* \cap E_{z,i}$; it holds for every edge of the window.
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, p. 19, Observation 3

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Observation 3, p. 19: a non-empty edge `e` inside the window `V_{z,i}` with
`diam(e) > d - k` meets both the first `k` vertices `L` and the last `k` vertices `R` of the
window. -/
theorem observation_3 (n d k z : ℕ) (i : ℤ) (e : Finset ℕ)
    (he : e ⊆ window n d z i) (hne : e.Nonempty) (hlong : (d : ℤ) - k < (diam e : ℤ)) :
    (e ∩ firstK (window n d z i) k).Nonempty ∧
    (e ∩ lastK (window n d z i) k).Nonempty := by sorry

end HyperMatchDelay.Batching
