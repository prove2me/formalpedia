-- Prove2me | Theorems.Thm_HyperMatchDelay_Batching_observation_1
-- name    : HyperMatchDelay.Batching.observation_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:59.595979+00:00
-- url     : https://prove2.me/theorems/b03ad1b7-b6b0-42d9-9f1f-e13803a78152
-- title:
--   Observation 1, p. 6 — every hyperedge e lies in E_z for at least d − diam(e) shifts z
-- statement:
--   Let $H = (V, E, w)$ be a shareability hypergraph with parameters $(n, d, k)$ and $d \ge 1$. For a shift $z \in \{0,\dots,d-1\}$ let $E_z = \bigcup_i E_{z,i}$ be the set of hyperedges contained in a single batch window $V_{z,i} = \{v \in [n] : z + id \le v \le z + (i+1)d - 1\}$. Then every hyperedge $e \in E$ survives the batching for many shifts:
--   $$ \sum_{z=0}^{d-1} \mathbb 1[e \in E_z] \;\ge\; d - \mathrm{diam}(e). $$
--
--   Since $\mathrm{diam}(e) < d$, every hyperedge lies in $E_z$ for at least one shift, and a hyperedge of diameter at most $d - k$ for at least $k$ shifts. This counting fact is what turns per-batch guarantees into the $1/d$ competitive ratio.
--
--   **Formalization Note** The left-hand side is the number of $z \in \{0,\dots,d-1\}$ with $e \in E_z$; $d - \mathrm{diam}(e)$ is a natural-number difference, exact here because $\mathrm{diam}(e) < d$.
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, p. 6, Observation 1

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Observation 1, p. 6: every hyperedge `e` of a shareability hypergraph lies in `E_z` for at
least `d - diam(e)` of the `d` shifts `z ∈ {0, …, d - 1}`. -/
theorem observation_1 (n d k : ℕ) (hd : 1 ≤ d) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w) (e : Finset ℕ) (he : e ∈ E) :
    d - diam e ≤ ((Finset.range d).filter (fun z => e ∈ shiftEdges E n d z)).card := by sorry

end HyperMatchDelay.Batching
