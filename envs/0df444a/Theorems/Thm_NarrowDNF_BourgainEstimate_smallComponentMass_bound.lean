-- Prove2me | Theorems.Thm_NarrowDNF_BourgainEstimate_smallComponentMass_bound
-- name    : NarrowDNF.BourgainEstimate.smallComponentMass_bound
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:51:19.575586+00:00
-- url     : https://prove2.me/theorems/06678db2-f3d0-4126-bf4b-ef4d0c2d95b8
-- title:
--   Small Fourier-component mass at a natural degree cutoff
-- statement:
--   Let \(\iota\) be finite, \(0<p<1\), and let \(f:\{0,1\}^{\iota}\to\{0,1\}\). Define \(\chi_S(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}\), \(\widehat f(S)=\mathbb E_p[f\chi_S]\), and \(f_S(x)=\widehat f(S)\chi_S(x)\), using independent Bernoulli measure \(\mu_p\). Let \(k\in\mathbb N\), \(k\ge5\), \(0<e\le1\), and \(0\le C\le k\). Assume the total independent-resampling influence \(I_p(f)\) is at most \(C\). For \(\eta=e^{10k}/3^{10k^2}\),
--   $$\mathbb E_p\sum_{|S|\le k}f_S(x)^2\mathbf1_{|f_S(x)|\le\eta}\le\frac{e^2}{2k}.$$
--   The empty support is included. This provides a factor-two margin in the small-component error budget. The bound is uniform in the dimension and the bias.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainEstimate.lean#L70-L89

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainComponents
import Definitions.Def_NarrowDNF_BourgainParameters
import Definitions.Def_NarrowDNF_Influence
import Theorems.Thm_NarrowDNF_BourgainEstimate_smallComponentMass_le_general
import Theorems.Thm_NarrowDNF_BourgainParameters_total_bound

namespace NarrowDNF.BourgainEstimate
end NarrowDNF.BourgainEstimate

namespace NarrowDNF.BourgainParameters
end NarrowDNF.BourgainParameters
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainEstimate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainEstimate.smallComponentMass_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) {k : ℕ} (hk : 5 ≤ k) {e C : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ k)
    (hI : Influence.totalInfluence p f ≤ C) :
    BourgainComponents.smallComponentMass p (fun x => Influence.boolValue (f x)) k
      (BourgainParameters.eta k e) ≤ e^2/(2*(k : ℝ)) := by sorry
