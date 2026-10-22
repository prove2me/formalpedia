-- Prove2me | Theorems.Thm_FullFormalization_D_pos
-- name    : FullFormalization.D_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:46:14.739995+00:00
-- url     : https://prove2.me/theorems/3cf68f19-e6d1-4ef8-a88a-8f5c23bb9650
-- title:
--   Strict positivity of $D_j$ on $0 \le j \le N+1$
-- statement:
--   For every $N \ge 1$ and every $0 \le j \le N+1$, the coefficient $D_N(j)$ is strictly positive:
--
--   $$0 < D_N(j) = \begin{cases} 2d_N + 1, & j = 0,\\[2pt] 2d_N - d_{j-1}, & j \ge 1,\end{cases} \qquad d_j = \frac{j(j+7)}{8}.$$
--
--   The two branches are treated separately. For $j = 0$ the capital value $2d_N+1$ is positive outright; for $j \ge 1$ the hypothesis $j \le N+1$ gives $j-1 \le N$, so monotonicity of $d$ yields $d_{j-1} \le d_N$ and hence $D_N(j) \ge d_N \ge d_1 = 1 > 0$. Together with (5.5), this is what makes every weight in the certificate strictly positive (source §13).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §13, eqs. (5.5) and (4.7)-(4.8); Lean: FullFormalization.Coefficients lines 143-165

-- Generated from F:/20261008/FullFormalization\FullFormalization\Coefficients.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.Coefficients

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 4 and 5.

  All scalar coefficient sequences of the rational-momentum Nesterov
  certificate, transcribed verbatim from the source:

    (4.1)  d_j = j (j+7) / 8
    (4.2)  tau = 1/(2 (2 d_N + 1)) = 2 / (N^2 + 7 N + 4)
    (4.3)  h_j = (j+2)/2 - j(j+1)(j+2) / (2 (N+1)(N+2))
    (4.4)  H_j = (j+1)(j+4)/4 - j(j+1)(j+2)(j+3) / (8 (N+1)(N+2))
    (4.7)  D_0 = 2 d_N + 1
    (4.8)  D_j = 2 d_N - d_{j-1}          (1 <= j <= N)
    (4.11) a_j = H_j / D_{j+1}            (0 <= j < N)
    (4.12) a_{-1} = 0,  a_N = 1
    (4.13) b_j = a_j - a_{j-1}            (0 <= j <= N)
    (3.2)  m_k = k / (k+3)

  Representation choices (recorded in DEPENDENCY_MAP.md, section 9, and in
  THEOREM_AUDIT.md):

  * Coefficients are real-valued.  Every division below is a division in the
    exact characteristic-zero field `R`; no floating point arithmetic and no
    finite enumeration is used anywhere.  All identities in
    `CoefficientIdentities.lean` are proved symbolically in `N` and `j`.

  * `D` is defined by the source's two-case definition: index `0` uses the
    separately-declared `D_0`, and the source explicitly warns (line 427) that
    formula (4.8) must not be extended mechanically to `j = 0`.  The Lean
    definition reproduces exactly that two-case split.

  * `a` uses the source's separate endpoint values: `a_N = 1` is *not* equal to
    `H_N / D_{N+1}`, so it is a genuine case split, not a convenience.

  * `a_{-1} = 0` is not an index of `a : Nat -> R`; it is absorbed into the
    definition of `b`, where `b_0 := a_0 - a_{-1} = a_0`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Theorems.Thm_FullFormalization_D_succ
import Theorems.Thm_FullFormalization_D_zero_capital
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_one

namespace FullFormalization

















/-! ## Basic closed forms used throughout

These are the elementary evaluations that every later module relies on.
They are consequences of the definitions, not extra assumptions. -/

























/-! ## `tau` vs `1 / (2 (2 d_N + 1))`  (source (4.2)) -/













end FullFormalization

open FullFormalization

theorem FullFormalization.D_pos (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ N + 1) : 0 < D N j := by sorry
