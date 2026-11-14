-- Prove2me | Theorems.Thm_NarrowDNF_Activation_controlled_monotonicization
-- name    : NarrowDNF.Activation.controlled_monotonicization
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:25:46.558739+00:00
-- url     : https://prove2.me/theorems/fb4366ef-730b-4fda-be7d-bbdf1f011f04
-- title:
--   Controlled monotonicization of an adaptive approximation
-- statement:
--   Let \(\iota\) be finite and let \(\mu_p\) be independent Bernoulli measure with \(0<p<1\). An activation family \(J\) has local tests on coordinate sets; write \(A_J(x)\) for the union of firing sets and \(\ell_p(J)=\sum_S|S|\Pr_p[J_S]\) for its load. Suppose its tests are increasing and only sets of size at most \(d\in\mathbb N\) fire. Let \(f,h:\{0,1\}^{\iota}\to\{0,1\}\), with \(f\) monotone and \(h\) determined by the active coordinates and their labels. Assume \(e,L\ge0\), \(\Pr_p[f\ne h]\le e\), and \(\ell_p(J)\le L\). For every \(\tau>0\), some coordinate set \(D\) and monotone function \(u\), measurable for \(J^D\), satisfy
--   $$\Pr_p[f\ne u]\le e+\tau,\qquad \mathbb E_p|A_{J^D}(x)|\le(2-p)^dL(1+e/\tau).$$
--   Here \(J^D\) evaluates activation tests after setting coordinates in \(D\) to one, while retaining the original input labels.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ControlledMonotonicization.lean#L27-L68

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_AdaptiveShift
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_ShiftProbability
import Theorems.Thm_NarrowDNF_Activation_load_forcing_le
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split
import Theorems.Thm_NarrowDNF_ProductMeasure_forcing_mass
import Theorems.Thm_NarrowDNF_ShiftProbability_one_coordinate_error_le
import Theorems.Thm_NarrowDNF_Weighted_select_two_budgets
import Theorems.Thm_NarrowDNF_monotone_of_coordinateMonotone

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.ShiftProbability
end NarrowDNF.ShiftProbability
noncomputable section
open NarrowDNF
open NarrowDNF
open NarrowDNF.Activation
open ProductMeasure ShiftProbability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.Activation.controlled_monotonicization {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {d : ℕ} {e L : ℝ} (_he0 : 0 ≤ e) (hL0 : 0 ≤ L)
    {f : Cube ι → Bool} (hf : Monotone f)
    {J : Activation ι} (hJ : J.Increasing) (hd : J.ArityLE d)
    {h : Cube ι → Bool} (hh : J.Measurable h)
    (he : error p f h ≤ e) (hL : J.load p ≤ L)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ (D : Finset ι) (u : Cube ι → Bool),
      Monotone u ∧ (J.force D).Measurable u ∧ error p f u ≤ e + τ ∧
      expectation p (fun x => (((J.force D).activeFinset x).card : ℝ)) ≤
        (2-p)^d * L * (1 + e / τ) := by sorry
