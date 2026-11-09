-- Prove2me | Theorems.Thm_GirthBethe_Sharp_local_transfer_coefficients
-- name    : GirthBethe.Sharp.local_transfer_coefficients
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:18:32.567908+00:00
-- url     : https://prove2.me/theorems/6d068750-7158-4510-962b-66d4da97c758
-- title:
--   Lemma 4.3 — coefficients $\alpha^v_{ef}$ satisfying (4.2) exist
-- statement:
--   Let $G=(L\sqcup R,E)$ be a finite simple bipartite graph, let $J_e^+,J_e^-\ge0$ be edge weights, and fix a vertex $v$. Put $J_v^\pm=\sum_{e\ni v}J_e^\pm$. Assume
--   $$J_v^-\le J_v^+,\qquad J_e^-\le\sum_{\substack{f\ni v\\f\ne e}}J_f^+\quad(e\ni v).$$
--   There exist nonnegative coefficients $\alpha^v_{ef}$ for distinct $e,f\ni v$ such that
--   $$\sum_{\substack{f\ni v\\f\ne e}}\alpha^v_{ef}=J_e^-,\qquad
--   \sum_{\substack{e\ni v\\e\ne f}}\alpha^v_{ef}\le J_f^+.$$
--   These coefficients are the local transfer weights in the auxiliary network of Definition 4.4. This formulation includes all weights obtained from a matching law by Definition 4.1 and the arbitrary-weight extension explicitly permitted on p. 12.
--
--   Differences from the source:
--   - encoding: a finite simple bipartite graph G = (L ⊔ R, E) → finite types L and R and an edge finset E ⊆ L × R; vertexWeight J v = ∑_{e ∋ v} J_e; reason: each edge has exactly one endpoint in each class; no extra graph condition is introduced
--   - generalization: the law-derived J_e^± of Definition 4.1 in the standing balanced-graph setting; p. 12 expressly also permits arbitrary nonnegative weights satisfying Lemma 4.2 → arbitrary nonnegative edge weights on any finite simple bipartite graph, with only the two local inequalities at the selected vertex; reason: the proof of Lemma 4.3 uses only these local inequalities; Lemma 4.2 supplies them for all law-derived instances, so the complete source result is recovered
--   - encoding: coefficients α^v_{ef} indexed by distinct incident edges → α defined on all edge pairs and constrained only on distinct pairs incident to v; reason: other values are never used
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 12, Lemma 4.3 (condition (4.2)); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_FlowNetwork

open Finset

namespace GirthBethe.Sharp

open scoped Classical in
/-- Lemma 4.3, using the arbitrary nonnegative weights allowed in the p. 12 preamble.
The two local inequalities of Lemma 4.2 imply existence of the coefficients (4.2). -/
theorem local_transfer_coefficients {L R : Type*} [Fintype L] [Fintype R]
    (E : Finset (L × R)) (Jp Jm : Edge E → ℝ)
    (hp : ∀ e, 0 ≤ Jp e) (hm : ∀ e, 0 ≤ Jm e) (v : L ⊕ R)
    (htotal : vertexWeight Jm v ≤ vertexWeight Jp v)
    (hoff : ∀ e : Edge E, Inc v e.1 →
      Jm e ≤ ∑ f with Inc v f.1 ∧ f ≠ e, Jp f) :
    ∃ α : Edge E → Edge E → ℝ, SatisfiesCoeffCond Jp Jm v α := by sorry

end GirthBethe.Sharp
