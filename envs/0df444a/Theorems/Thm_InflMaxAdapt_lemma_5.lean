-- Prove2me | Theorems.Thm_InflMaxAdapt_lemma_5
-- name    : InflMaxAdapt.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:35:18.479239+00:00
-- url     : https://prove2.me/theorems/faa6b1c5-6685-43d7-b334-e8835ecba749
-- title:
--   Lemma 5 — three-point inequality with sets
-- statement:
--   In the undirected-edge representation with edge probabilities $q \in [0,1]$, for all vertices $u, v \in V$ and every set $S \subseteq V$,
--   $$
--   \mathbb P(u \leftrightarrow v,\ v \leftrightarrow S)^2 \;\le\; 8\, \mathbb P(u \leftrightarrow v)\, \mathbb P(v \leftrightarrow S)\, \mathbb P(u \leftrightarrow S).
--   $$
--   It extends Gladkov's inequality (2) to a set in place of one of the three vertices and bounds the excess of weakly connected seeds.
--
--   Differences from the source:
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Lemma 5, printed p.7 (PDF p.8)

import Mathlib
import Definitions.Def_InflMaxAdapt_kappa
import Definitions.Def_InflMaxAdapt_Conn

open MeasureTheory

namespace InflMaxAdapt

/-- Lemma 5, the three-point inequality with sets (printed p.7 = PDF p.8, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): for all
vertices `u, v` and every set `S ⊆ V`,
`P(u ↔ v, v ↔ S)² ≤ 8 P(u ↔ v) P(v ↔ S) P(u ↔ S)`, where `κ(w) = P(w ↔ S)`. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (u v : V) (S : Finset V) :
    edgeProb q (fun E => Conn E u v ∧ ConnSet E v S) ^ 2 ≤
      8 * edgeProb q (fun E => Conn E u v) * kappa q S v * kappa q S u := by sorry

end InflMaxAdapt
