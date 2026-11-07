-- Prove2me | Theorems.Thm_IncrementalER_lemma_3_7
-- name    : IncrementalER.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:38.315208+00:00
-- url     : https://prove2.me/theorems/55bfcb79-1dbf-44c6-a28d-3fce7bbe0c76
-- title:
--   Lemma 3.7, p.12 — $q^G_{V\setminus\{v\}}(u)=q^G(u)+q^G(v)c_{uv}/d_v$
-- statement:
--   Let $G=(V,E,c)$ be a connected graph and $u\neq v$ vertices. Eliminating $v$ changes the excess of $u$ by
--
--   $$q^G_{V\setminus\{v\}}(u)=q^G(u)+q^G(v)\,\frac{c_{uv}}{d_v},$$
--
--   where $d_v$ is the capacitated degree of $v$. The excess of the remaining vertices thus evolves as the right-hand side does in Gaussian elimination. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - encoding: u ranges over the remaining vertices V \ {v} → u ≠ v as a hypothesis; reason: the same range
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 3.7, p.12; Definition 3.5, p.12; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond

namespace IncrementalER

/-- **Lemma 3.7** (excess under elimination of one vertex).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 3.7, p.12; Definition 3.5, p.12; connectivity assumption, p.10.

For a connected graph `G = (V, E, c)` and vertices `u ≠ v`,
`q^G_{V∖{v}}(u) = q^G(u) + q^G(v) c_uv / d_v`.

**Formalization Note.** The lemma is about the remaining vertices `u ∈ V \ {v}`, hence `u ≠ v`;
`d_v = ∑_w c(v, w)` is the capacitated degree. -/
theorem lemma_3_7 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (u v : V) (huv : u ≠ v) :
    excessT c (Finset.univ.erase v) u = excess c u + excess c v * c u v / capDeg c v := by sorry

end IncrementalER
