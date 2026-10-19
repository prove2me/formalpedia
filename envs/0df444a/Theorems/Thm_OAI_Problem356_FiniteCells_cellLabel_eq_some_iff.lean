-- Prove2me | Theorems.Thm_OAI_Problem356_FiniteCells_cellLabel_eq_some_iff
-- name    : OAI.Problem356.FiniteCells.cellLabel_eq_some_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:54:35.730515+00:00
-- url     : https://prove2.me/theorems/0224aadb-b83a-4d42-906e-62808fdc1568
-- title:
--   The label of a point in a disjoint family
-- statement:
--   Let $(A_i)$ be a pairwise disjoint family of sets, and let $\mathrm{label}(x)$ be some $i$ with $x\in A_i$ if one exists, and none otherwise. Then for every $x$ and $i$,
--   $$
--   \mathrm{label}(x)=i\iff x\in A_i .
--   $$
--
--   For disjoint cells the chosen label is the unique cell containing the point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/PartitionLabel.lean#L20-L36

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
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel

open OAI OAI.Problem356 OAI.Problem356.FiniteCells
universe uX uIndex
open Set MeasureTheory

theorem OAI.Problem356.FiniteCells.cellLabel_eq_some_iff {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (x : X) (i : ι) :
    cellLabel A x = some i ↔ x ∈ A i := by sorry
