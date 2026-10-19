-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_matrix_defect_rounding
-- name    : OAI.AsymptoticallyMinimalLittlewood.matrix_defect_rounding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:49:08.430811+00:00
-- url     : https://prove2.me/theorems/f97173f2-616d-4aac-964e-de141b697ba5
-- title:
--   Mass-sensitive rounding of a fractional vector to a $0/1$ vector with row discrepancy $1+O\big(\sqrt{\mu\log(2|\beta|/\mu)}\big)$
-- statement:
--   Let $\alpha$ and $\beta$ be finite sets with $|\alpha|\le|\beta|$, and let $A=(A_{ik})_{i\in\beta,\,k\in\alpha}$ be a real matrix with $|A_{ik}|\le 1$ for all $i,k$. Let $p\in[0,1]^{\alpha}$, and let $\mu>0$ with $2\mu\le|\beta|$ and $\sum_{k\in\alpha}p_k\le\mu$. Then there is $p'\in\{0,1\}^{\alpha}$ with $\sum_{k\in\alpha}p'_k\le\sum_{k\in\alpha}p_k$ such that, for every row $i\in\beta$,
--
--   $$
--   \Bigl|\sum_{k\in\alpha}A_{ik}\,(p'_k-p_k)\Bigr|\le 1+24576\sqrt{\mu\log\frac{2|\beta|}{\mu}} .
--   $$
--
--   This is a rounding (discrepancy) theorem whose error depends on the total mass $\mu$ of the fractional vector rather than on the number of coordinates: when $p$ is supported on few coordinates or is small, the rounding error is correspondingly small. It is applied to rows given by the real and imaginary parts of the monomials $z^k$ at the points of a fine grid of roots of unity, in order to round a polynomial with coefficients in $[-1,1]$ to one with coefficients $\pm 1$.
--
--   **Formalization Note** The rounded vector $p'$ is real-valued with each value equal to $0$ or $1$. Since $2|\beta|/\mu\ge 4$, the logarithm is positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L960-L1033

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.matrix_defect_rounding {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (p : α → ℝ) (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, p k) ≤ μ) :
    ∃ p' : α → ℝ, (∀ k, p' k = 0 ∨ p' k = 1) ∧ (∑ k, p' k) ≤ ∑ k, p k ∧
      ∀ i, |∑ k, A i k * (p' k - p k)| ≤
        1 + 24576 * Real.sqrt (μ * Real.log (2 * Fintype.card β / μ)) := by sorry
