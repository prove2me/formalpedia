-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyclic_model
-- name    : KnodelPrimeCordial.cyclic_model
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:01:40.932266+00:00
-- url     : https://prove2.me/theorems/f2b0db6e-363e-437e-b2c1-0ae83a7d8462
-- title:
--   §1, p.3 — $W_{3,n}$ is the $n$-cycle $v_0\cdots v_{n-1}$ with the chords $v_{2i}v_{2i+5}$
-- statement:
--   Let $n\ge 8$ be even, and name the vertices of the Knödel graph $W_{3,n}$ by $v_{2j}=(1,j)$ and $v_{2j-1}=(2,j)$, indices read modulo $n$. Then
--
--   $$
--   V(W_{3,n})=\{v_i:0\le i\le n-1\},\qquad E(W_{3,n})=\{v_iv_{i+1}:0\le i\le n-1\}\cup\{v_{2i}v_{2i+5}:0\le i\le n/2-1\}.
--   $$
--
--   In other words, $i\mapsto v_i$ is a bijection from $\{0,\dots,n-1\}$ onto the vertex set of $W_{3,n}$, and two vertices $v_a,v_b$ are adjacent in $W_{3,n}$ exactly when $\{a,b\}$ is an edge of the cyclic model (consecutive indices, or an even index $2i$ and $2i+5$, modulo $n$).
--
--   This identification is what lets the paper write its labelings as functions of a single index $i$ and analyse them residue class by residue class.
--
--   Differences from the source:
--   - encoding: Δ = 3 and even n ≥ 8 → hypotheses Even n and 8 ≤ n; reason: the paper's domain stated as binders
--   - encoding: vertex (i, j) with i = 1, 2 → Fin 2 × Fin (n/2) with sides 1, 2 as 0, 1; reason: Lean convention; same graph
--   - encoding: V(W3,n) = {v_i} and the displayed edge set → the naming map vtx is bijective and carries the adjacency of cyc n exactly onto that of knodel 3 n; reason: this is the meaning of the display with the paper's specific naming v_{2j} = (1, j), v_{2j−1} = (2, j)
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), §1, p.3 (PDF p.3), display after "for ∆ = 3 and even n ≥ 8, we have"

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_vtx

namespace KnodelPrimeCordial

/-- **Cyclic description of `W_{3,n}`** (Haque, Khanam, Shahriar, *Prime cordial labeling of
Knödel graph*, manuscript (2026), §1, p.3, display): "For W∆,n, let v2j represent vertex (1,j)
and v2j−1 represent vertex (2,j). In this paper, the vertex labels are read modulo n unless
specified otherwise. From the definition of the Knödel graph, for ∆ = 3 and even n ≥ 8, we have
V(W3,n) = {vi : 0 ≤ i ≤ n − 1}, E(W3,n) = {vivi+1 : 0 ≤ i ≤ n − 1} ∪ {v2iv2i+5 : 0 ≤ i ≤ n/2 − 1}."

For every even `n ≥ 8`, the naming map `i ↦ v_i` (`vtx`) is a bijection from `{0, …, n−1}`
onto the vertices of `W_{3,n}`, and it carries the edges of the cyclic model `cyc n` exactly
onto the edges of `W_{3,n}`.

**Formalization Note** The domain "Δ = 3 and even n ≥ 8" is `Even n ∧ 8 ≤ n`. The map is the
paper's specific one (`v_{2j} = (1, j)`, `v_{2j−1} = (2, j)`, sides as `Fin 2` values `0, 1`),
not an arbitrary isomorphism. -/
theorem cyclic_model (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) :
    Function.Bijective (vtx n (by omega)) ∧
      ∀ a b : Fin n, (cyc n).Adj a b ↔ (knodel 3 n).Adj (vtx n (by omega) a) (vtx n (by omega) b) := by sorry

end KnodelPrimeCordial
