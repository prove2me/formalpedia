-- Prove2me | Theorems.Thm_NarrowDNF_ProductMeasure_forcing_mass
-- name    : NarrowDNF.ProductMeasure.forcing_mass
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:31.074563+00:00
-- url     : https://prove2.me/theorems/a96f0c89-52a5-40a3-9e0f-0956c3e66446
-- title:
--   Coordinatewise OR sends two Bernoulli product cubes to bias 2p minus p squared
-- statement:
--   Let $I$ be finite, let $p\in\mathbb R$, and let $z\in\{0,1\}^I$. For the finite product weights $w_p$,
--   $$
--   \sum_{x,d\in\{0,1\}^I}\mathbf1_{\{x\lor d=z\}}w_p(x)w_p(d)
--   =w_{2p-p^2}(z).
--   $$
--   The OR is taken coordinatewise. When $0\le p\le1$, this says that the OR of two independent $p$-biased cubes is a product cube of bias $2p-p^2$. The displayed finite-sum identity itself holds for every real $p$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L207-L223

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ProductMeasure_sum_prod_two_coordinates

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.ProductMeasure.forcing_mass (p : ℝ) (z : ι → Bool) :
    (∑ x : ι → Bool, ∑ d : ι → Bool,
      if (fun i => x i || d i) = z then weight p x * weight p d else 0) =
        weight (2*p-p^2) z := by sorry
