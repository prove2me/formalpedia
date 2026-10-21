-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_absorption_iff_nonsingular
-- name    : MatrixAnalytic.PH.absorption_iff_nonsingular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:48.373774+00:00
-- url     : https://prove2.me/theorems/6ad85fb1-0b5d-4a04-a054-1cf3ed0dfaa9
-- title:
--   Theorem 2.4.3 — absorption a.s. from every phase iff $T$ is nonsingular, and $(-T^{-1})_{ij}$ is the expected time in phase $j$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be a continuous PH representation on a finite phase set: $T_{ii} < 0$, $T_{ij} \ge 0$ for $i \ne j$, $\boldsymbol t = -T\mathbf 1 \ge 0$, and $(\tau_0, \boldsymbol\tau)$ is a probability vector. Let $J$ be the Markov process on $\{0\} \cup \{\text{phases}\}$ with generator $Q = \begin{bmatrix} 0 & \mathbf 0 \\ \boldsymbol t & T\end{bmatrix}$ and transition function $\exp(Qx)$. Then:
--
--   1. Absorption into state $0$ occurs with probability 1 from every phase $i$ if and only if $T$ is nonsingular:
--   $$\Big(\forall i:\ \lim_{x\to\infty}\exp(Qx)_{i0} = 1\Big) \iff \det T \ne 0.$$
--   2. If $T$ is nonsingular, then for all phases $i, j$ the expected total time $E_{ij} = \int_0^\infty \exp(Qx)_{ij}\,dx$ spent in phase $j$ before absorption, starting from phase $i$, is finite and
--   $$E_{ij} = (-T^{-1})_{ij}.$$
--
--   The theorem turns a probabilistic property of the process into an algebraic property of $T$ and gives $-T^{-1}$ its meaning; it underlies the convention of p. 44 that $T$ is nonsingular, and every moment and transform formula after it (Remark 2.4.4, Eqs. (2.12)–(2.13)).
--
--   **Formalization Note** The process is encoded by its transition function `NormedSpace.exp (x • Q)` on the finite state space `Option ι` (absorbing state `none`). Absorption with probability 1 from phase $i$ is the limit $\exp(Qx)_{i0} \to 1$. The expected time $E_{ij}$ is a lower Lebesgue integral in $[0, \infty]$, so an infinite expected time is $\infty$ and not a junk real; the conclusion asserts $E_{ij} \ne \infty$ and that its real value is $(-T^{-1})_{ij}$ (which in particular yields $-T^{-1} \ge 0$, Remark 2.4.4). Nonsingularity is `IsUnit T.det`; under it Mathlib's `T⁻¹` is the true inverse. Invertibility is never assumed for the equivalence. The initial vector $\boldsymbol\tau$ plays no role in the conclusion but is part of "a PH$\{\boldsymbol\tau, T\}$ distribution".
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 43, Theorem 2.4.3

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.4.3 (Latouche–Ramaswami, p. 43): for a `PH(τ, T)` distribution, absorption into
state 0 occurs with probability 1 from every phase iff `T` is nonsingular; and then
`(−T⁻¹)_ij` is the expected total time spent in phase `j` before absorption, starting from
phase `i` (in particular that expected time is finite). -/
theorem absorption_iff_nonsingular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) :
    ((∀ i, AbsorbedAS T i) ↔ IsUnit T.det) ∧
    (IsUnit T.det → ∀ i j : ι,
      expectedTime T i j ≠ ⊤ ∧ (expectedTime T i j).toReal = (-T⁻¹) i j) := by sorry

end MatrixAnalytic.PH
