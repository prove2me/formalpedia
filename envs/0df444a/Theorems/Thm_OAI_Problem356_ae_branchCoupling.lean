-- Prove2me | Theorems.Thm_OAI_Problem356_ae_branchCoupling
-- name    : OAI.Problem356.ae_branchCoupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:37:28.541671+00:00
-- url     : https://prove2.me/theorems/dafc1ca3-bbfc-47c4-a654-e78abf0b3f8f
-- title:
--   Cyclically invariant properties of the branches hold for the coupling
-- statement:
--   For a measure $\nu$ on $\mathbb{R}^3$ and maps $H_1,\dots,H_4$, the branch coupling is $\frac16$ times the sum of the pushforwards of $\nu$ under the six maps $x\mapsto(x,H_1x,H_2x)$, $(H_1x,H_2x,x)$, $(H_2x,x,H_1x)$, $(x,H_3x,H_4x)$, $(H_3x,H_4x,x)$, $(H_4x,x,H_3x)$. Let $P$ be a measurable property of triples that is invariant under the cyclic shift,
--   $$
--   P(x,y,z)\implies P(y,z,x) ,
--   $$
--   with $P(x,H_1x,H_2x)$ and $P(x,H_3x,H_4x)$ for $\nu$-almost every $x$. Then $P$ holds almost everywhere for the branch coupling.
--
--   Properties checked on the two branch graphs, such as contact with the dual certificate, transfer to the coupling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/BranchCoupling.lean#L154-L180

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.ae_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) {P : Triple → Prop} (hP : MeasurableSet {t | P t})
    (hcycle : ∀ x y z, P (x, (y, z)) → P (y, (z, x)))
    (h12 : ∀ᵐ x ∂nu, P (x, (H1 x, H2 x)))
    (h34 : ∀ᵐ x ∂nu, P (x, (H3 x, H4 x))) :
    ∀ᵐ t ∂branchCoupling nu H1 H2 H3 H4, P t := by sorry
