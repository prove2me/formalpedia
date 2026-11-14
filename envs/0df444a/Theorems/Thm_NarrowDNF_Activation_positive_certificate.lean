-- Prove2me | Theorems.Thm_NarrowDNF_Activation_positive_certificate
-- name    : NarrowDNF.Activation.positive_certificate
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:02:30.237984+00:00
-- url     : https://prove2.me/theorems/fd707b7e-7cc7-4960-beb1-5e2c5af1d0a3
-- title:
--   Positive active labels form an acceptance certificate
-- statement:
--   Let \(\iota\) be a coordinate set and \(J\) a family of local activation tests indexed by finite subsets of \(\iota\). Assume each test is increasing under the coordinatewise order. Write \(A_J(x)\) for the union of sets whose tests fire at input \(x\). Let \(u:\{0,1\}^{\iota}\to\{0,1\}\) be monotone and constant on adaptive atoms, where an atom records the active union and its input labels. If \(u(x)=1\), then every input \(y\) preserving the positive active labels is accepted:
--   $$\bigl(\forall i\in A_J(x),\ x_i=1\Rightarrow y_i=1\bigr)\quad\Longrightarrow\quad u(y)=1.$$
--   Thus the positive labels in the active union constitute a certificate for acceptance.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L70-L92

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation
open NarrowDNF
open NarrowDNF
open NarrowDNF.Activation
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι]

theorem NarrowDNF.Activation.positive_certificate {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    {x : Cube ι} (hx : u x = true) {y : Cube ι}
    (hy : ∀ i ∈ J.active x, x i = true → y i = true) : u y = true := by sorry
