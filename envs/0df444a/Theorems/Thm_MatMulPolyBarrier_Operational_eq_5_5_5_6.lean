-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_eq_5_5_5_6
-- name    : MatMulPolyBarrier.Operational.eq_5_5_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:16.139304+00:00
-- url     : https://prove2.me/theorems/056a608a-2aec-491b-92cd-424de67d3626
-- title:
--   §5.6, Eqs. (5.5)–(5.6) — identities for the exponents $p_i$
-- statement:
--   Let $\theta\in\Theta$ and $\{i,j,k\}=\{1,2,3\}$, with $p_i=\theta_i/((1-\theta_j)(1-\theta_k))$ as in (5.2). Then $p_i=\theta_i/(\theta_i+\theta_j\theta_k)$, so $0<p_i<1$; moreover
--   $$p_i(1-\theta_j)+p_j(1-\theta_i)=\frac{\theta_i+\theta_j}{1-\theta_k}=1\qquad(5.5)$$
--   and in particular $p_i+p_j=1+p_i\theta_j+p_j\theta_i>1$ and
--   $$(1-p_i)+p_i\theta_j=p_j(1-\theta_i)\qquad(5.6).$$
--   These identities are used throughout the proof of Proposition 5.8.
--
--   Differences from the source:
--   - encoding: indices {i, j, k} = {1, 2, 3} → i j k : Fin 3 pairwise distinct, p_i = pExp θ i; reason: Lean indexing, same instances
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 40, §5.6, Eqs. (5.5)–(5.6) (proof of Proposition 5.8)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- §5.6, Eqs. (5.5)–(5.6), p. 40 (proof of Proposition 5.8): for `θ ∈ Θ` and
`{i, j, k} = {1, 2, 3}`: `p_i = θ_i / (θ_i + θ_j θ_k)`, `0 < p_i < 1`,
`p_i(1 − θ_j) + p_j(1 − θ_i) = (θ_i + θ_j)/(1 − θ_k) = 1` (5.5),
`p_i + p_j = 1 + p_i θ_j + p_j θ_i > 1` and `(1 − p_i) + p_i θ_j = p_j (1 − θ_i)` (5.6). -/
theorem eq_5_5_5_6 (θ : Fin 3 → ℝ) (hθ : InTheta θ) (i j k : Fin 3) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    pExp θ i = θ i / (θ i + θ j * θ k) ∧
    0 < pExp θ i ∧ pExp θ i < 1 ∧
    pExp θ i * (1 - θ j) + pExp θ j * (1 - θ i) = (θ i + θ j) / (1 - θ k) ∧
    (θ i + θ j) / (1 - θ k) = 1 ∧
    pExp θ i + pExp θ j = 1 + pExp θ i * θ j + pExp θ j * θ i ∧
    1 < pExp θ i + pExp θ j ∧
    (1 - pExp θ i) + pExp θ i * θ j = pExp θ j * (1 - θ i) := by sorry

end MatMulPolyBarrier.Operational
