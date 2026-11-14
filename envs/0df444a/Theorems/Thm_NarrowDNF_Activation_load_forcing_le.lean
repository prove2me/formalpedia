-- Prove2me | Theorems.Thm_NarrowDNF_Activation_load_forcing_le
-- name    : NarrowDNF.Activation.load_forcing_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:17:02.753676+00:00
-- url     : https://prove2.me/theorems/ec46c805-6cff-4b77-a520-82ac154d536f
-- title:
--   Activation load under Bernoulli forcing
-- statement:
--   Let \(\iota\) be a finite coordinate set and \(J\) an activation family: each event \(J_S\) depends only on bits in its finite indexing set \(S\subseteq\iota\). For \(q\in[0,1]\), define its load by \(\ell_q(J)=\sum_{S\subseteq\iota}|S|\Pr_q[J_S]\), where \(\Pr_q\) is independent Bernoulli measure. Suppose \(d\in\mathbb N\) and no set larger than \(d\) ever fires. Then, for every \(p\in[0,1]\),
--   $$\ell_{2p-p^2}(J)\le(2-p)^d\ell_p(J).$$
--   The new bias is the probability that at least one of two independent Bernoulli \(p\) bits is one. The estimate controls the load increase caused by this forcing distribution, including both endpoint biases.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/LoadTransport.lean#L112-L131

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict
import Theorems.Thm_NarrowDNF_ProductMeasure_weight_forcing_le

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open NarrowDNF
open NarrowDNF.Activation
open ProductMeasure
attribute [local instance] Classical.propDecidable

theorem NarrowDNF.Activation.load_forcing_le (J : Activation ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (hd : J.ArityLE d) :
    J.load (2*p-p^2) ≤ (2-p)^d * J.load p := by sorry
