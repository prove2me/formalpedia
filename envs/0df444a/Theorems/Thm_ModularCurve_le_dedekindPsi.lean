-- Prove2me | Theorems.Thm_ModularCurve_le_dedekindPsi
-- name    : ModularCurve.le_dedekindPsi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/0aa03680-9cd6-5b88-8722-f756559b369a
-- title:
--   Dedekind ψ dominates its argument
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. Here `dedekindPsi N` is defined as the sum $\sum N/d$, taken over those $d$ in the finite set of divisors of $N$ that are squarefree, the division being natural-number division (exact on divisors). The theorem asserts that $N \le \mathtt{dedekindPsi } N$, i.e. that the Dedekind $\psi$-function, presented in the form $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, is bounded below by $N$ itself. The hypothesis $N \neq 0$ is genuinely needed: the divisor set of $0$ is empty in this convention, so the sum defining `dedekindPsi 0` is $0$, and the inequality would fail for $N = 0$ as stated with natural-number subtraction-free comparison.
--
--   This is the elementary lower bound $N \le \psi(N)$ for the Dedekind $\psi$-function, which computes the index $[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]$. It serves the numerical layer for the modular curves $X_0(N)$, and is used for the positivity statement [`ModularCurve.dedekindPsi_pos`](thm.html#ModularCurve.dedekindPsi_pos) and in the identification of a relative dimension with the index in [`ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero`](thm.html#ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_le_dedekindPsi.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.le_dedekindPsi (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by sorry
