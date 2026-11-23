-- Prove2me | Theorems.Thm_NeuralCollapseCE_ce_quadratic_form_bound
-- name    : NeuralCollapseCE.ce_quadratic_form_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:11:24.197111+00:00
-- url     : https://prove2.me/theorems/458ba0fc-5a3a-4f45-8480-c83d7f8d3fb8
-- title:
--   Theorem 1, eq. (15): the bound $n\sum_i\langle v_i,u_i\rangle-\langle V,U\rangle\le n^2$ and its equality case
-- statement:
--   Let $u_1,\dots,u_n,v_1,\dots,v_n\in\mathbb{R}^d$ be unit vectors, $U=\sum_iu_i$, $V=\sum_iv_i$. Then
--
--   $$n\sum_{i=1}^n\langle v_i,u_i\rangle-\langle V,U\rangle\ \le\ n^2,$$
--
--   and equality holds if and only if $U=0$ and $v_i=u_i$ for every $i$.
--
--   The left side is $\vec v^{\top}\big((nI_n-\mathbf 1_n\mathbf 1_n^{\top})\otimes I_d\big)\vec u$ (eq. 14), whose matrix has eigenvalues $n$ and $0$; the bound is inequality (15), and the equality case is the paper's discussion after (15): equality forces $\vec u$ into the eigenspace for $n$ and $\vec v$ to be a positive multiple of $\vec u$.
--
--   **Formalization Note** The paper phrases the equality case as "$\vec u$ is an eigenvector for the eigenvalue $n$ and $\vec v=\lambda\vec u$, $\lambda>0$"; for unit vectors this is the same as $U=0$ and $v=u$.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 3 (proof of Theorem 1), eqs. (14)-(15) and the equality discussion following (15), p. 8

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem ce_quadratic_form_bound {n d : ℕ} (u v : Fin n → Vec d)
    (hu : IsUnitConfig u) (hv : IsUnitConfig v) :
    (n : ℝ) * ∑ i, inner ℝ (v i) (u i) - inner ℝ (∑ i, v i) (∑ i, u i) ≤ (n : ℝ) ^ 2 ∧
      ((n : ℝ) * ∑ i, inner ℝ (v i) (u i) - inner ℝ (∑ i, v i) (∑ i, u i) = (n : ℝ) ^ 2 ↔
        (∑ i, u i = 0 ∧ v = u)) := by sorry

end NeuralCollapseCE
