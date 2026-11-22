-- Prove2me | Theorems.Thm_GroupMetrization_struble
-- name    : GroupMetrization.struble
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:11.024801+00:00
-- url     : https://prove2.me/theorems/baf93780-6a16-48ff-887d-97e8ab197bf6
-- title:
--   Struble's theorem: a locally compact Hausdorff group is second countable iff it has a left-invariant metric inducing its topology with compact closed balls
-- statement:
--   **Struble's theorem on metrics in locally compact groups.** Let $G$ be a Hausdorff locally compact topological group (not necessarily abelian). Then the following are equivalent:
--
--   1. $G$ is second countable;
--   2. there is a metric $d$ on $G$ which induces the topology of $G$, is left-invariant,
--   $$d(gx,gy)=d(x,y)\qquad\text{for all }g,x,y\in G ,$$
--   and all of whose balls are bounded, i.e. every closed ball $\{y\in G:\ d(x,y)\le r\}$ is compact.
--
--   Here a subset $B\subset G$ is called bounded if for every neighbourhood $U$ of the neutral element there are finitely many $g_1,\dots,g_N\in G$ with $B\subset g_1U\cup\dots\cup g_NU$; in a Hausdorff locally compact group this means that $B$ has compact closure, so "all balls are bounded" says exactly that all closed balls are compact (the metric is proper).
--
--   The source recalls this in Remark A.5.2.9; it is the structural reason why the second countable locally compact abelian groups of the source (idele groups, idele class groups and their norm-one subgroups) carry invariant metrics with relatively compact balls, exhausting the group.
--
--   **Formalization Note.** The metric is a `MetricSpace G` structure `d` whose induced topology equals the given topology of $G$; left-invariance is stated for `d.dist`, and boundedness of the balls as compactness of every `Metric.closedBall x r` for the metric `d`. The implication from 2 to 1 is elementary (a proper metric space is second countable).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 571, Remark A.5.2.9; classical reference: R. A. Struble, Metrics in locally compact groups, Compositio Math. 28 (1974), no. 3, pp. 217-222, Theorem, p. 217 (as cited by the paper)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace GroupMetrization

theorem struble (G : Type*) [Group G] [t : TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    SecondCountableTopology G ↔
      ∃ d : MetricSpace G, d.toUniformSpace.toTopologicalSpace = t ∧
        (∀ g x y : G, d.dist (g * x) (g * y) = d.dist x y) ∧
        ∀ (x : G) (r : ℝ), IsCompact (@Metric.closedBall G d.toPseudoMetricSpace x r) := by sorry

end GroupMetrization
