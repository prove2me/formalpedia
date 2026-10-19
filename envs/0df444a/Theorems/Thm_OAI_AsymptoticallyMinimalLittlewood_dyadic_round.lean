-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_dyadic_round
-- name    : OAI.AsymptoticallyMinimalLittlewood.dyadic_round
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:48:26.407002+00:00
-- url     : https://prove2.me/theorems/ed157762-0062-4a9f-83b9-d33b09936160
-- title:
--   Iterated dyadic rounding of a low-mass vector on the $2^{-j}$ grid to a $0/1$ vector
-- statement:
--   Let $\alpha$ and $\beta$ be finite sets with $|\alpha|\le|\beta|$, let $A=(A_{ik})_{i\in\beta,\,k\in\alpha}$ be a real matrix with $|A_{ik}|\le 1$ for all $i,k$, and let $\mu>0$ with $2\mu\le|\beta|$. Fix an integer $j\ge 0$. For every $a:\alpha\to\mathbb{Z}_{\ge 0}$ with $a_k\le 2^{j}$ for all $k$ and $\sum_{k\in\alpha}a_k/2^{j}\le\mu$, there is $b:\alpha\to\{0,1\}$ such that $\sum_{k\in\alpha}b_k\le\sum_{k\in\alpha}a_k/2^{j}$ and, for every row $i\in\beta$,
--
--   $$
--   \Bigl|\sum_{k\in\alpha}A_{ik}\Bigl(b_k-\frac{a_k}{2^{j}}\Bigr)\Bigr|\le 8192\cdot 3\Bigl(1-\Bigl(\frac34\Bigr)^{j}\Bigr)\sqrt{\mu\log\frac{2|\beta|}{\mu}} .
--   $$
--
--   Thus a vector in $[0,1]^{\alpha}$ whose coordinates are multiples of $2^{-j}$ and whose total mass is at most $\mu$ can be rounded to a $0/1$ vector, without increasing the mass, so that every row of $A$ moves by at most $24576\sqrt{\mu\log(2|\beta|/\mu)}$, uniformly in the depth $j$. The error is governed by the mass $\mu$ rather than by the number of coordinates $|\alpha|$, which is what makes the rounding effective for vectors of small total mass.
--
--   **Formalization Note** The numerators $a_k$ and the rounded values $b_k$ are natural numbers; the condition $b_k\in\{0,1\}$ is stated as $b_k\le 1$. The quantifier over $a$ sits after $j$, which allows induction on $j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L919-L958

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.dyadic_round {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β) (j : ℕ) :
    ∀ a : α → ℕ, (∀ k, a k ≤ 2 ^ j) →
      (∑ k, (a k : ℝ) / 2 ^ j) ≤ μ →
      ∃ b : α → ℕ, (∀ k, b k ≤ 1) ∧
        (∑ k, (b k : ℝ)) ≤ (∑ k, (a k : ℝ) / 2 ^ j) ∧
        ∀ i, |∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)| ≤
          8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) := by sorry
