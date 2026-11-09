-- Prove2me | Theorems.Thm_InflMaxAdapt_eq_4
-- name    : InflMaxAdapt.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:34:27.563311+00:00
-- url     : https://prove2.me/theorems/daec8e61-e821-4cf5-8c1b-504896184b44
-- title:
--   Eq. (4) — the Kozma–Nitzan inequality
-- statement:
--   Let $V$ be any finite set and let the unordered pairs of $V$ be live edges independently with probabilities $q \in [0,1]$. For all vertices $u, v \in V$ and every nonempty set $T \subseteq V$,
--   $$
--   \mathbb P(u \leftrightarrow v) \;\ge\; \mathbb P(u \leftrightarrow T)\, \min_{t \in T} \mathbb P(t \leftrightarrow v).
--   $$
--   This is the connection inequality conjectured by Kozma and Nitzan [KN24] (Conjecture 1 there) and since proved [Gou26], in the form the paper states it. The proof of (5) applies it to the graph obtained by contracting $S$ to a single vertex, which is why it is stated for every finite vertex set.
--
--   Differences from the source:
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
--   - encoding: min over t ∈ T → Finset.inf' over the nonempty T; reason: the minimum of a nonempty finite family
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Eq. (4), printed p.8 (PDF p.9)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeProb
import Definitions.Def_InflMaxAdapt_ConnSet

open MeasureTheory

namespace InflMaxAdapt

/-- Eq. (4), the Kozma–Nitzan inequality [KN24; Gou26] as stated on printed p.8 (PDF p.9) of
de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5): for every finite vertex set `V`, every independent bond percolation on it with edge
probabilities `q ∈ [0,1]`, all vertices `u, v` and every nonempty set `T ⊆ V`,
`P(u ↔ v) ≥ P(u ↔ T) · min_{t ∈ T} P(t ↔ v)`. -/
theorem eq_4 {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (u v : V) (T : Finset V) (hT : T.Nonempty) :
    edgeProb q (fun E => Conn E u v) ≥
      edgeProb q (fun E => ConnSet E u T) * T.inf' hT (fun t => edgeProb q (fun E => Conn E t v)) := by sorry

end InflMaxAdapt
