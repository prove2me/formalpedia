-- Prove2me | Theorems.Thm_GroupMetrization_birkhoff_kakutani
-- name    : GroupMetrization.birkhoff_kakutani
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:08.127931+00:00
-- url     : https://prove2.me/theorems/8afb17f3-3302-4326-95a1-8e278301d89a
-- title:
--   Birkhoff–Kakutani theorem: a Hausdorff topological group is first countable iff its topology is given by a left-invariant metric
-- statement:
--   **Birkhoff–Kakutani metrization theorem for topological groups.** Let $G$ be a Hausdorff topological group (not necessarily abelian, not necessarily locally compact). Then the following are equivalent:
--
--   1. $G$ is first countable, i.e. the neutral element (equivalently every point) has a countable base of neighbourhoods;
--   2. there is a metric $d$ on $G$ which induces the topology of $G$ and is left-invariant:
--   $$d(gx,gy)=d(x,y)\qquad\text{for all }g,x,y\in G .$$
--
--   In particular a Hausdorff topological group is metrizable if and only if it is first countable, and the metric can then be chosen left-invariant.
--
--   The source recalls this in Remark A.5.2.9 as the first step towards invariant metrics on the second countable locally compact abelian groups it works with (idele groups and their quotients), which it uses to obtain complete metrics and Borel fundamental domains.
--
--   **Formalization Note.** The metric is a `MetricSpace G` structure `d` whose induced topology equals the given topology of $G$ (`d.toUniformSpace.toTopologicalSpace = t`); left-invariance is stated for its distance function `d.dist`. The implication from 2 to 1 is the trivial one (metric spaces are first countable); the content is the implication from 1 to 2.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 571, Remark A.5.2.9; classical references: G. Birkhoff, A note on topological groups, Compositio Math. 3 (1936), pp. 427-430, Theorem, p. 428; R. A. Struble, Metrics in locally compact groups, Compositio Math. 28 (1974), no. 3, pp. 217-222, Lemma 1, p. 217 (as cited by the paper)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace GroupMetrization

theorem birkhoff_kakutani (G : Type*) [Group G] [t : TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] :
    FirstCountableTopology G ↔
      ∃ d : MetricSpace G, d.toUniformSpace.toTopologicalSpace = t ∧
        ∀ g x y : G, d.dist (g * x) (g * y) = d.dist x y := by sorry

end GroupMetrization
