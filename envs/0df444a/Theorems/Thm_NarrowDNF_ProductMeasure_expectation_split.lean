-- Prove2me | Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split
-- name    : NarrowDNF.ProductMeasure.expectation_split
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:19.756823+00:00
-- url     : https://prove2.me/theorems/43418322-bf89-44ae-9ffe-eb3f94f64022
-- title:
--   One-coordinate Fubini formula for finite Bernoulli expectation
-- statement:
--   Let $I$ be finite, $i\in I$, $p\in\mathbb R$, and $F:\{0,1\}^I\to\mathbb R$. Write $z^{i,b}$ for the extension of $z\in\{0,1\}^{I\setminus\{i\}}$ whose $i$-th bit is $b$. With product-weight expectation on each coordinate set,
--   $$
--   \mathbb E_pF=(1-p)\mathbb E_p[F(z^{i,0})]+p\mathbb E_p[F(z^{i,1})].
--   $$
--   The identity is algebraic and needs no assumption $0\le p\le1$. In that range it expresses conditioning on one independent Bernoulli coordinate and is the basic disintegration step for the shift estimates.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L159-L177

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.ProductMeasure.expectation_split (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) :
    expectation p F =
      (1-p) * expectation p (fun z => F (insertBit i false z)) +
        p * expectation p (fun z => F (insertBit i true z)) := by sorry
