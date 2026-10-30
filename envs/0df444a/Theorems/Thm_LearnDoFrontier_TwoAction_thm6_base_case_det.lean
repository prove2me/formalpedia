-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_thm6_base_case_det
-- name    : LearnDoFrontier.TwoAction.thm6_base_case_det
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:38.520005+00:00
-- url     : https://prove2.me/theorems/349a2ba3-541b-4cfd-95da-c15cf826e8b4
-- title:
--   Proof of Theorem 6 (Complete), (1) Base case, EC p. 13 — det Y when every B-root is simple
-- statement:
--   Let $z^A_1, \dots, z^A_{d^A} \in \mathbb C$ be distinct with multiplicities $m^A_i \ge 1$, and let $z^B_1, \dots, z^B_{d^B} \in \mathbb C$ be distinct, each with multiplicity $m^B_j = 1$. Let $Y = (Y^A, Y^B)$ be the matrix of Theorem 6 (Complete) built from these points, with $N = \sum_i m^A_i + d^B$ rows; here $Y^B$ has entries $(z^B_j)^{N-1-k}$. Then
--   $$\det Y = \prod_{1\le i<j\le d^A}(z^A_j - z^A_i)^{m^A_i m^A_j}\cdot\prod_{i=1}^{d^A}\prod_{j=1}^{d^B}(1 - z^A_i z^B_j)^{m^A_i}\cdot\prod_{1\le i<j\le d^B}(z^B_i - z^B_j),$$
--   and if moreover $|z^A_i| < 1$ and $|z^B_j| < 1$ for all $i, j$, then $\det Y \ne 0$.
--
--   This is the base case of the induction on the B-multiplicities that proves the determinant formula of Theorem 6 (Complete).
--
--   **Formalization Note** The points are arbitrary, not necessarily roots of $f^A_\theta$, $f^B_\theta$, as the induction requires. The determinant is the general formula of Theorem 6 (Complete) specialized to $m^B_j = 1$.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), EC p. 13 (PDF p. 56), proof of Theorem 6 (Complete), (1) Base case

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra

namespace LearnDoFrontier.TwoAction

theorem thm6_base_case_det {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ) (zB : Fin dB → ℂ)
    (hzA : Function.Injective zA) (hmA : ∀ i, 1 ≤ mA i) (hzB : Function.Injective zB) :
    (Ymat zA mA zB (fun _ => 1)).det = detFormula zA mA zB (fun _ => 1) ∧
      ((∀ i, ‖zA i‖ < 1) → (∀ j, ‖zB j‖ < 1) → (Ymat zA mA zB (fun _ => 1)).det ≠ 0) := by sorry

end LearnDoFrontier.TwoAction
