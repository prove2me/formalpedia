-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_dyadic_round_step
-- name    : OAI.AsymptoticallyMinimalLittlewood.dyadic_round_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:47:47.955028+00:00
-- url     : https://prove2.me/theorems/096379e0-ca4f-4ef2-8902-3f06d2227a10
-- title:
--   One dyadic rounding step: from denominator $2^{j+1}$ to $2^{j}$ with no mass increase and small row discrepancy
-- statement:
--   Let $\alpha$ and $\beta$ be finite sets with $|\alpha|\le|\beta|$, and let $A=(A_{ik})_{i\in\beta,\,k\in\alpha}$ be a real matrix with $|A_{ik}|\le 1$ for all $i,k$. Let $j\ge 0$ be an integer and let $a:\alpha\to\mathbb{Z}_{\ge 0}$ satisfy $a_k\le 2^{j+1}$ for every $k$. Let $\mu>0$ with $2\mu\le|\beta|$, and assume the mass bound $\sum_{k\in\alpha}a_k/2^{j+1}\le\mu$. Then there is $b:\alpha\to\mathbb{Z}_{\ge 0}$ such that
--
--   1. $b_k\le 2^{j}$ for every $k\in\alpha$;
--   2. $\sum_{k\in\alpha}b_k/2^{j}\le\sum_{k\in\alpha}a_k/2^{j+1}$;
--   3. for every row $i\in\beta$,
--
--   $$
--   \Bigl|\sum_{k\in\alpha}A_{ik}\Bigl(\frac{b_k}{2^{j}}-\frac{a_k}{2^{j+1}}\Bigr)\Bigr|\le 8192\Bigl(\frac34\Bigr)^{j+1}\sqrt{\mu\log\frac{2|\beta|}{\mu}} .
--   $$
--
--   Viewing $(a_k/2^{j+1})_k$ as a point of $[0,1]^{\alpha}$ with dyadic coordinates of denominator $2^{j+1}$, the step replaces it by a point with denominator $2^{j}$, without increasing the total mass, so that every row of $A$ changes by an amount that decays geometrically in $j$. Iterating the step from fine to coarse scales rounds a fractional vector to a $0/1$ vector.
--
--   **Formalization Note** The numerators $a_k,b_k$ are natural numbers (`α → ℕ`), and $|\alpha|,|\beta|$ are `Fintype.card α`, `Fintype.card β`. Since $2|\beta|/\mu\ge 4$, the logarithm is positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L810-L917

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.dyadic_round_step {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (a : α → ℕ) (j : ℕ) (ha : ∀ k, a k ≤ 2 ^ (j + 1))
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ≤ μ) :
    ∃ b : α → ℕ, (∀ k, b k ≤ 2 ^ j) ∧
      (∑ k, (b k : ℝ) / 2 ^ j) ≤ (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ∧
      ∀ i, |∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))| ≤
        8192 * ((3 / 4) ^ (j + 1) * Real.sqrt
          (μ * Real.log (2 * Fintype.card β / μ))) := by sorry
