-- Prove2me | Theorems.Thm_FullFormalization_Pbeta_pos
-- name    : FullFormalization.Pbeta_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:31:06.905244+00:00
-- url     : https://prove2.me/theorems/bda91fd6-2d03-4586-8552-dfbb541b03c0
-- title:
--   Positivity of the $\beta_j$ numerator polynomial $P(u,v)$
-- statement:
--   The numerator polynomial produced by the manuscript substitution (16.1) is strictly positive for all nonnegative integers $u$ and $v$:
--   $$P(u,v) \;=\; \sum_{i=0}^{8} u^{i}\,P_{i}(v) \;>\; 0, \qquad u, v \in \mathbb{N}.$$
--   $P$ is the polynomial, of degree eight in $u$, whose coefficients $P_{i}(v)$ in $v$ are all nonnegative with a strictly positive leading constant; the parameters are $u = j-1$ and $v = N-j-2$ from (16.1). Strict positivity holds because every monomial $u^{i}v^{k}$ carries a strictly positive coefficient and a nonnegative exponent.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §16, eq. (16.1)-(16.3); Lean: FullFormalization.Positivity lines 290-294

-- Generated from F:/20261008/FullFormalization\FullFormalization\Positivity.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.Positivity

  Source sections 13-16: positivity of every weight in the certificate.

    * `h_pos`      — (13.1)
    * `H_pos`      — `H` is strictly increasing from `H_0 = 1`, by (5.1)
    * `D_pos`      — `D_j > 0` on the valid range
    * `a_pos`      — Lemma 13.1, first half
    * `b_pos`      — Lemma 13.1, second half; uses the identity
                     `b_j = H_j (j+3)/(4 D_j D_{j+1}) + h_j/D_j` derived from
                     (5.1) and (5.5), so positivity is immediate from `H, h, D > 0`
    * `alpha_pos`  — section 14
    * `betaT_eq`, `betaT_pos` — (15.1), (15.2), (15.3)
    * `beta_eq_P`, `beta_pos` — (16.2)-(16.4), via the source's substitution
                     `j = u + 1`, `N = u + v + 3`, `u, v >= 0`, and the explicit
                     polynomials `Pbeta (16.2)`, `Qbeta (16.3)` with all-positive
                     coefficients (`Pbeta_pos`, `Qbeta_pos`)

  None of these is a finite enumeration: the running index and `N` stay
  universally quantified throughout, and every statement is proved
  symbolically.
-/

import Mathlib
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_Positivity

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace FullFormalization

/-! ### (13.1) `h_j > 0` -/





/-! ### `H_j > 0` -/





/-! ### `a_j > 0` and `b_j > 0`  (Lemma 13.1) -/









/-! ### Section 14: `alpha_j > 0` -/



/-! ### Section 15: `β_T > 0`  —  (15.1), (15.2), (15.3)

`β_T = ½ (a_{N-1} - (m_{N-1} + b_N)²)` by (6.5).  Evaluating the three pieces in
closed form — `a_{N-1} = N(N+7)/(N²+9N+6)`, `m_{N-1} = (N-1)/(N+2)`,
`b_N = 1 - a_{N-1}` — gives the rational function (15.1); the source then
substitutes `N = u + 2` to put the numerator in the all-positive form (15.2). -/







/-! ### Section 16: `β_j > 0`  —  (16.1)-(16.4)

Source (16.1) substitutes `j = u + 1`, `N = u + v + 3` with `u, v >= 0`, under
which `β_j` (6.3) becomes the ratio `P(u,v)/Q(u,v)` of the two polynomials
below; both have all coefficients of one sign, so `β_j > 0` is immediate.

The two coefficient lists are those of `scripts/gen_beta_data.py`, which
regenerates them exactly from the definitions of `a`, `b`, `h`, `H`, `D`, `m`,
`d` in `Coefficients.lean` (source (4.1)-(4.13)).  The source prints the
denominator factor `u² + 4uv + 2v² + 15u + 26v + 42`, which is `8 * D_{j+2}`
under the substitution; the factor `128 (u+4)² (u+v+4)(u+v+5)` likewise collects
the denominators `8 (N+1)(N+2)` of `H`, `2 (N+1)(N+2)` of `h` and `k + 3 = u+4`
of `m`.  Both `P` and `Q` are the sign-flipped (positive) versions: the raw
SymPy output carries an overall sign on each. -/













end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem FullFormalization.Pbeta_pos (u v : ℕ) : 0 < Pbeta u v := by sorry
