-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_matrix_signing_raw
-- name    : OAI.AsymptoticallyMinimalLittlewood.matrix_signing_raw
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:46:00.766014+00:00
-- url     : https://prove2.me/theorems/bf28107e-ed37-424f-a1be-fa4ae999ae0b
-- title:
--   Full $\pm1$ signing of a bounded matrix with discrepancy $4096\sqrt{n\log(16m/n)}$
-- statement:
--   Let $K$ and $I$ be finite sets with $n=|K|$ and $m=|I|$ elements (columns and rows), and let $B=(B_{ik})_{i\in I,\,k\in K}$ be a real matrix with $|B_{ik}|\le1$ for all $i,k$. Assume $n\le m$. Then there is a sign vector $\xi\in\{-1,1\}^K$ such that
--
--   $$
--   \Big|\sum_{k\in K}B_{ik}\,\xi_k\Big|\le4096\sqrt{n\log\frac{16m}{n}}\qquad\text{for every row } i\in I.
--   $$
--
--   This is a square-root-logarithmic discrepancy bound for matrices with at least as many rows as columns, in which the logarithm involves only the aspect ratio $m/n$ (a uniformly random signing combined with a union bound over the rows gives only $O(\sqrt{n\log m})$). In the construction of flat Littlewood polynomials it is the engine for rounding real coefficients of modulus at most $1$ to signs while simultaneously controlling many linear functionals (for instance the values of the polynomial on a grid of the unit circle).
--
--   **Formalization Note** The statement carries an explicit natural number $n$ with `Fintype.card α = n` and quantifies over all finite types $\alpha,\beta$ (rows $\beta$, columns $\alpha$); this form is used for strong induction on $n$, and it is equivalent to the statement for all finite $K,I$. For $n=0$ the bound reads $0$, since Lean evaluates $16m/0=0$ and $\log 0=0$; the row sums are then empty and equal to $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L630-L711

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.matrix_signing_raw (n : ℕ) :
    ∀ {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β], Fintype.card α = n →
      ∀ B : β → α → ℝ, (∀ i k, |B i k| ≤ 1) → Fintype.card α ≤ Fintype.card β →
      ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧
        ∀ i, |∑ k, B i k * ξ k| ≤ 4096 * Real.sqrt ((Fintype.card α : ℝ) *
          Real.log (16 * Fintype.card β / Fintype.card α)) := by sorry
