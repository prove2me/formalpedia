-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_hall_orientation
-- name    : OptimalAgnosticPAC.Learner.hall_orientation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:32.883828+00:00
-- url     : https://prove2.me/theorems/c4288704-7e4f-49ec-a718-a8399db07e5e
-- title:
--   Hall orientation criterion (§2): capacities on induced edge counts give an orientation
-- statement:
--   Let $G=(V,E)$ be a finite graph and let $c_x\ge0$, $x\in V$, be integer capacities such that for every $W\subseteq V$,
--   $$|E_G(W)|\le\sum_{x\in W}c_x.$$
--   Then every edge can be assigned to one of its endpoints so that, for every $x\in V$, at most $c_x$ edges are assigned to $x$. Moreover, there is an orientation $\sigma$ of $G$ with $\mathrm{out}(x;\sigma)\le c_x$ for every $x\in V$.
--
--   The paper uses this form of Hall's theorem to turn the edge bound for the cube into an orientation.
--
--   Differences from the source:
--   - reading: a finite graph G = (V, E) whose edges are subsets e ⊆ V → a finite SimpleGraph; reason: the paper applies the criterion only to the cube and writes edges as sets with two endpoints
--   - encoding: an orientation chooses a head σ(e) ∈ e for each edge → a total map σ : Sym2 V → V with σ e ∈ e on the edge set; reason: values off the edge set are never read
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §2, PDF p. 6 (printed p. 5), citing Diestel, Graph Theory, Theorem 2.1.2

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- The Hall orientation criterion of §2, PDF p. 6: under the capacity condition every edge can be
assigned to one of its endpoints with at most `c x` edges assigned to `x`, and there is an
orientation with outdegree at most `c x` at every `x`. -/
theorem hall_orientation {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → ℕ)
    (hc : ∀ W : Finset V, (inducedEdges G W).card ≤ ∑ x ∈ W, c x) :
    (∃ a : Sym2 V → V, (∀ e ∈ G.edgeSet, a e ∈ e) ∧
      ∀ x, (G.edgeFinset.filter (fun e => a e = x)).card ≤ c x) ∧
    (∃ σ : Sym2 V → V, IsOrientation G σ ∧ ∀ x, outdegree G σ x ≤ c x) := by sorry

end OptimalAgnosticPAC.Learner
