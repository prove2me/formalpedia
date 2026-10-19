-- Prove2me | Theorems.Thm_OAI_Problem356_exists_uniform_compact_separation
-- name    : OAI.Problem356.exists_uniform_compact_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:41:43.342661+00:00
-- url     : https://prove2.me/theorems/7cf58932-ce8b-48c1-8faa-98b96b0e2669
-- title:
--   Disjoint compact sets are uniformly separated
-- statement:
--   Let $(K_i)_{i\in\iota}$ be finitely many pairwise disjoint compact subsets of a metric space. Then there is $\eta>0$ with
--   $$
--   d(x,y)\ge\eta\qquad\text{whenever }x\in K_i,\ y\in K_j,\ i\ne j .
--   $$
--
--   Empty components and an empty index set are allowed. This gives the separation needed to keep the Coulomb cost bounded on couplings concentrated on distinct components.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CompactSeparation.lean#L11-L37

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uAlpha uIndex

theorem OAI.Problem356.exists_uniform_compact_separation {α : Type uAlpha} {ι : Type uIndex} [MetricSpace α] [Finite ι]
    (K : ι → Set α) (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, eta ≤ dist x y := by sorry
