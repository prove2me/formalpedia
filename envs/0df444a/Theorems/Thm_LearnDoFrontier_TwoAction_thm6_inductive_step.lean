-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_thm6_inductive_step
-- name    : LearnDoFrontier.TwoAction.thm6_inductive_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:40.547994+00:00
-- url     : https://prove2.me/theorems/a1be47df-9057-4cfb-a29e-d5e2af9c3c08
-- title:
--   Proof of Theorem 6 (Complete), (2) Inductive step, EC p. 13 — det Y = (1/τ!) dτ/dtτ det Ŷ(t) at t = z^B_1
-- statement:
--   Let $z^A_1, \dots, z^A_{d^A}$ be distinct with multiplicities $m^A_i \ge 1$, and $z^B_1, \dots, z^B_{d^B}$ distinct with multiplicities $m^B_j \ge 1$; let $Y = (Y^A, Y^B)$ be the matrix of Theorem 6 (Complete), with $N = \sum m^A_i + \sum m^B_j$ rows. Fix a B-point $z^B_j$ with $m^B_j \ge 2$ and let $\hat Y(t)$ be $Y$ with the first column of the block of $z^B_j$ (the column $\tau = m^B_j - 1$) replaced by $(t^{N-1-k})_{k=0,\dots,N-1}$. Then, with $\tau = m^B_j - 1$,
--   $$\det Y = \frac{1}{\tau!}\,\frac{d^\tau}{dt^\tau}\det\hat Y(t)\Big|_{t = z^B_j}.$$
--
--   In the paper the root is $z^B_1$, chosen without loss of generality as a root of maximal multiplicity. The identity expresses a repeated root's column as a derivative of a simple root's column, which reduces the determinant formula to the inductive hypothesis with one more simple "nominal root" $t$.
--
--   **Formalization Note** The statement is for any B-point with multiplicity at least $2$, which is the paper's $z^B_1$ up to relabelling. The derivative is `iteratedDeriv` of the complex function $t \mapsto \det\hat Y(t)$.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), EC p. 13 (PDF p. 56), proof of Theorem 6 (Complete), (2) Inductive step

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra

namespace LearnDoFrontier.TwoAction

theorem thm6_inductive_step {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ)
    (zB : Fin dB → ℂ) (mB : Fin dB → ℕ)
    (hzA : Function.Injective zA) (hmA : ∀ i, 1 ≤ mA i)
    (hzB : Function.Injective zB) (hmB : ∀ j, 1 ≤ mB j) (j : Fin dB) (hj : 2 ≤ mB j) :
    (Ymat zA mA zB mB).det =
      iteratedDeriv (mB j - 1) (fun t : ℂ => (Yhat zA mA zB mB j (by omega) t).det) (zB j)
        / ((mB j - 1).factorial : ℂ) := by sorry

end LearnDoFrontier.TwoAction
