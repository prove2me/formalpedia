-- Prove2me | Theorems.Thm_InflMaxAdapt_eq_2
-- name    : InflMaxAdapt.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:34:09.03998+00:00
-- url     : https://prove2.me/theorems/7f38d6dd-088f-41c0-8d11-008e3b71de1e
-- title:
--   Eq. (2) — Gladkov's three-point inequality
-- statement:
--   Let $V$ be any finite set and let the unordered pairs of $V$ be live edges independently with probabilities $q \in [0,1]$. For all vertices $u, v, z \in V$,
--   $$
--   \mathbb P(u \leftrightarrow z,\ v \leftrightarrow z)^2 \;\le\; 8\, \mathbb P(u \leftrightarrow v)\, \mathbb P(u \leftrightarrow z)\, \mathbb P(v \leftrightarrow z).
--   $$
--   This is the three-point inequality of Gladkov [Gla24, Thm. 6.2] as the paper states it. It bounds the probability that three vertices lie in one cluster by the three pairwise connection probabilities; the proof of Lemma 5 applies it to a graph with an added vertex, which is why it is stated for every finite vertex set.
--
--   Differences from the source:
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), proof of Lemma 5, Eq. (2), printed p.7 (PDF p.8)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeProb
import Definitions.Def_InflMaxAdapt_Conn

open MeasureTheory

namespace InflMaxAdapt

/-- Eq. (2), the three-point inequality of Gladkov [Gla24, Thm. 6.2] as stated in the proof of
Lemma 5 (printed p.7 = PDF p.8, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): for every finite vertex set `V`, every independent bond
percolation on it with edge probabilities `q ∈ [0,1]`, and all vertices `u, v, z`,
`P(u ↔ z, v ↔ z)² ≤ 8 P(u ↔ v) P(u ↔ z) P(v ↔ z)`. -/
theorem eq_2 {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (u v z : V) :
    edgeProb q (fun E => Conn E u z ∧ Conn E v z) ^ 2 ≤
      8 * edgeProb q (fun E => Conn E u v) * edgeProb q (fun E => Conn E u z) *
        edgeProb q (fun E => Conn E v z) := by sorry

end InflMaxAdapt
