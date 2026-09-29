-- Prove2me | Theorems.Thm_ModularCurve_dedekindPsi_pos
-- name    : ModularCurve.dedekindPsi_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/607c1d4d-f64f-5dde-8549-a2bf11e49376
-- title:
--   Positivity of ψ(N) for N ≠ 0
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. The quantity `dedekindPsi N` is defined as the sum, over those divisors $d$ of $N$ that are squarefree, of the natural-number quotient $N/d$; for $N \neq 0$ this is the usual Dedekind function $\psi(N) = N\prod_{p \mid N}(1 + 1/p)$, the summands being indexed by the squarefree divisors $d$ of $N$ and $N/d$ being an exact division. The assertion is that this natural number is strictly positive, i.e. $0 < \psi(N)$. (For $N = 0$ the divisor set is empty and the sum would be $0$, so the hypothesis $N \neq 0$ is needed.)
--
--   This is the elementary positivity statement for the Dedekind $\psi$ function, the multiplicative function giving the index $[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]$ and hence the degree of the covering $X_0(N) \to X(1)$. It serves to licence division by $\psi(N)$ in the genus and Riemann–Hurwitz computations for $X_0(N)$, and is cited widely throughout the development of the modular curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dedekindPsi_pos.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.dedekindPsi_pos (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N := by sorry
