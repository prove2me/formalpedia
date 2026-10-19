-- Prove2me | Theorems.Thm_OAI_Problem356_exists_compact_small_partition
-- name    : OAI.Problem356.exists_compact_small_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:54:06.69798+00:00
-- url     : https://prove2.me/theorems/048bbdad-30e7-443d-a423-0ae28b2b0f5b
-- title:
--   Finite Borel partitions of a compact set into small pieces
-- statement:
--   Let $K$ be a compact subset of a metric space with its Borel structure, and $\delta>0$. Then there are finitely many pairwise disjoint Borel sets $A_1,\dots,A_n\subseteq K$ with
--   $$
--   \bigcup_iA_i=K,\qquad d(x,y)<\delta\ \text{ for }x,y\in A_i .
--   $$
--
--   Empty cells are permitted. Small cells allow a coupling to be approximated by a graph cell by cell.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CompactPartition.lean#L19-L57

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure

open OAI OAI.Problem356
universe uX uIndex
open Set MeasureTheory Metric

theorem OAI.Problem356.exists_compact_small_partition {X : Type uX} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : Set X} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : Fin n → Set X),
      (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = K ∧
      (∀ i, A i ⊆ K) ∧
      (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y < δ) := by sorry
