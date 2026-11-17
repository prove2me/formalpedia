-- Prove2me | Theorems.Thm_LatticePrepro_mul_le_sum_of_sum_prod_inv_le
-- name    : LatticePrepro.mul_le_sum_of_sum_prod_inv_le
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:10:14.18366+00:00
-- url     : https://prove2.me/theorems/72eac717-3848-4f78-88e6-2e78c337a99a
-- title:
--   Theorem 6.4, inequality (31) — a bound on $\sum_r\prod_j\lambda_{r,j}^{-1}$ forces a large average of the $\lambda_{r,j}$
-- statement:
--   Let $R$ be a finite set, let $q\ge0$ be an integer, and let $\lambda_{r,j}>0$ be real numbers for $r\in R$ and $1\le j\le q$. Let $t>0$ be a real number with
--   $$\Bigl(\sum_{r\in R}\prod_{j=1}^{q}\lambda_{r,j}^{-1}\Bigr)\cdot t^{q}\le|R| .$$
--   Then
--   $$|R|\cdot q\cdot t\le\sum_{r\in R}\sum_{j=1}^{q}\lambda_{r,j}.$$
--
--   In the soundness proof of Theorem 6.4, $R=\{0,1\}^{\mathsf R}$ is the set of random strings, $q=\mathsf q$, $\lambda_{r,j}=|\Lambda_{u_{r,j}}|$ is the size of the list at the $j$-th query of $r$, and $t=\mathsf s^{-1/\mathsf q}$. The hypothesis is the first inequality of (31), $\mathsf s\ge2^{-\mathsf R}\sum_r\prod_j|\Lambda_{u_{r,j}}|^{-1}$. The conclusion is $\overline\Lambda\ge\mathsf s^{-1/\mathsf q}$ for the average list size $\overline\Lambda$, which is what the other two inequalities of (31) give.
--
--   **Formalization Note.** The paper obtains the conclusion from Jensen's inequality for the exponential and then for the logarithm. The Lean proof applies $\log y\le y-1$, for each $r$, to the $q+1$ positive numbers $\lambda_{r,1}/t,\dots,\lambda_{r,q}/t$ and $t^{q}\prod_j\lambda_{r,j}^{-1}$, whose product is $1$, and sums over $r$. The statement also covers $q=0$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), proof of Theorem 6.4 (\label{thm:pcp-reduction}), soundness, second and third inequalities of (31) (\label{eq:pcp-list-bound}); Lean: LatticePrepro/PCP/Inequality.lean, LatticePrepro.mul_le_sum_of_sum_prod_inv_le

import Mathlib

open Finset

theorem LatticePrepro.mul_le_sum_of_sum_prod_inv_le {R : Type*} [Fintype R] {q : ℕ} (lam : R → Fin q → ℝ)
    (hlam : ∀ r j, 0 < lam r j) {t : ℝ} (ht : 0 < t)
    (h : (∑ r, ∏ j, (lam r j)⁻¹) * t ^ q ≤ Fintype.card R) :
    (Fintype.card R : ℝ) * q * t ≤ ∑ r, ∑ j, lam r j := by sorry
