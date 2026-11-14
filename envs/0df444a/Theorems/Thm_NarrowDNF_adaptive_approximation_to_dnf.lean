-- Prove2me | Theorems.Thm_NarrowDNF_adaptive_approximation_to_dnf
-- name    : NarrowDNF.adaptive_approximation_to_dnf
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:44.91365+00:00
-- url     : https://prove2.me/theorems/b3672f6f-ce78-4a05-b8b2-7d68ded303ed
-- title:
--   An increasing adaptive representation yields a narrow monotone DNF
-- statement:
--   Let $I$ be finite, $0<p<1$, $\varepsilon>0$, $L\ge0$, and $d\in\mathbb N$. Let $f,h$ be Boolean functions with $f$ monotone. Suppose $J$ is an increasing local activation family, no activation of size above $d$ fires, and $h$ is constant on its adaptive atoms. Assume $\Pr_p(f\ne h)\le\varepsilon/4$ and $\operatorname{load}_p(J)=\sum_S|S|\Pr_p(J_S\text{ fires})\le L$. There is a finite family $\mathcal T$ of positive conjunctions such that
--   $$
--   \forall T\in\mathcal T:\ |T|\le\left\lceil\frac{4\,2^dL}{\varepsilon}\right\rceil,
--   \qquad \Pr_p\left[f\ne\bigvee_{T\in\mathcal T}\bigwedge_{i\in T}x_i\right]\le\varepsilon.
--   $$
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/AdaptiveApproximation.lean#L13-L49

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Definitions.Def_NarrowDNF_CertificateBounds
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_MainStatements
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Activation_controlled_monotonicization
import Theorems.Thm_NarrowDNF_Activation_positive_certificate
import Theorems.Thm_NarrowDNF_Activation_truncatedDNF_error_bound

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open NarrowDNF
open ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.adaptive_approximation_to_dnf {p ε L : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hε : 0 < ε) (hL0 : 0 ≤ L) {d : ℕ} {f h : Cube ι → Bool}
    (hf : Monotone f) {J : Activation ι} (hJ : J.Increasing)
    (hd : J.ArityLE d) (hh : J.Measurable h)
    (he : error p f h ≤ ε/4) (hL : J.load p ≤ L) :
    ∃ terms : Finset (Finset ι),
      (∀ T ∈ terms, T.card ≤ Nat.ceil (4 * (2 : ℝ)^d * L / ε)) ∧
      error p f (evalDNF terms) ≤ ε := by sorry
