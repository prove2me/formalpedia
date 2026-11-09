-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_image_membership_lower_bound
-- name    : GraphIsoTesting.FixedGraph.image_membership_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:17.248119+00:00
-- url     : https://prove2.me/theorems/30f1bb5b-ec7d-449f-ad53-d15d67532cce
-- title:
--   Theorem 2.2 — Hardness of image membership
-- statement:
--   Fix real constants $0<\rho,\delta<1$. There are $\beta>0$ and $m_0$ depending only on these fixed constants such that the following holds for every $m\ge m_0$, every $k$, and every binary $m\times k$ matrix $A$. If $k\le(1-\rho)m$ and every set of at most $\delta m$ rows is linearly independent, then any randomized adaptive coordinate tester $T$ for membership in $\operatorname{Im}(A)$, with two-sided success at least $2/3$ and maximum query bound $q$, satisfies
--
--   $$q>\delta m.$$
--
--   Its soundness promise is the strict condition $D_A(b)>\beta m$. The constants are uniform over dimensions, matrices, and testers; there is no sparsity hypothesis. This supplies the hard base problem for the graph reduction, while preserving the theorem for all $\rho,\delta$ rather than only $\rho=1/2$.
--
--   Differences from the source:
--   - encoding: for every sufficiently large n and more than δn coordinate queries → an explicit uniform threshold m₀ and the real comparison δm < q in the shared PMF tree model; reason: m denotes the equation count; no rounding changes the strict query bound or the β-far promise
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 5, Theorem 2.2

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_BinarySystems

namespace GraphIsoTesting.FixedGraph

theorem image_membership_lower_bound (ρ δ : ℝ)
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ β : ℝ, 0 < β ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (k : ℕ) (A : BinaryMatrix m k), (k : ℝ) ≤ (1 - ρ) * (m : ℝ) →
        IndependentRowsUpTo A (δ * (m : ℝ)) →
        ∀ (q : ℕ) (T : RandomizedTester (Fin m) Bit q),
          IsImageTester A β T → δ * (m : ℝ) < (q : ℝ) := by sorry

end GraphIsoTesting.FixedGraph
