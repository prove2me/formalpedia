-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_5_2
-- name    : MatrixLeeSidford.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:03.660426+00:00
-- url     : https://prove2.me/theorems/15b75cf6-beb7-4f0f-9dbc-a86e3e484cc1
-- title:
--   Lemma 5.2 — trace powers along a symmetric exponential curve
-- statement:
--   Let $Z$ and $J$ be real symmetric $k\times k$ matrices, let $s\ge1$ be an integer, and define
--   $$
--   Z(t)=e^{tJ/2}Ze^{tJ/2},\qquad Y=\tfrac12(JZ+ZJ),\qquad g(t)=\frac1{2s}\operatorname{tr}\big[Z(t)^{2s}\big].
--   $$
--   Then
--   $$
--   g''(0)=2\sum_{a=0}^{s-1}\big\|Z^aYZ^{s-1-a}\big\|_F^2\le 2s\operatorname{tr}\big[Z^{2s}J^2\big]\qquad(5.4)
--   $$
--   and
--   $$
--   |g'''(0)|\le 20s\,\|J\|_{op}\,g''(0).\qquad(5.5)
--   $$
--   This curvature bound is the engine behind the Hessian and third-derivative estimates of the barrier.
--
--   Differences from the source:
--   - encoding: e^{tJ/2}, g'', g''' → LowRankMEG.mexp ((t/2) • J) (published spectral exponential cfc Real.exp), iteratedDeriv 2 and 3 at 0; reason: same objects for symmetric J
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 5.2, Eqs. (5.4)–(5.5), p.38

import Mathlib
import Definitions.Def_LowRankMEG_mexp
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_LiqPremiaEq_opNorm

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 5.2 (Trace powers along a symmetric exponential curve)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.38). Let `Z, J`
be real symmetric matrices of the same order, `s ≥ 1` an integer, `Z(t) := e^{tJ/2} Z e^{tJ/2}`,
`Y := ½(JZ + ZJ)`, `g(t) := (1/(2s)) tr[Z(t)^{2s}]`. Then
`g''(0) = 2 ∑_{a=0}^{s−1} ‖Z^a Y Z^{s−1−a}‖_F² ≤ 2s tr[Z^{2s} J²]` (5.4) and
`|g‴(0)| ≤ 20s ‖J‖_op g''(0)` (5.5).

**Formalization Note** `e^{tJ/2}` is `LowRankMEG.mexp ((t/2) • J)`; `g''`, `g‴` are `iteratedDeriv`. -/
theorem lemma_5_2 {k : ℕ} (Z J : Matrix (Fin k) (Fin k) ℝ) (hZ : Z.IsHermitian)
    (hJ : J.IsHermitian) (s : ℕ) (hs : 1 ≤ s) :
    let Zt : ℝ → Matrix (Fin k) (Fin k) ℝ := fun t => LowRankMEG.mexp ((t / 2) • J) * Z * LowRankMEG.mexp ((t / 2) • J)
    let Y := (1 / 2 : ℝ) • (J * Z + Z * J)
    let g : ℝ → ℝ := fun t => (1 / (2 * (s : ℝ))) * ((Zt t) ^ (2 * s)).trace
    iteratedDeriv 2 g 0 = 2 * ∑ a ∈ Finset.range s, LowRankMEG.frobNorm (Z ^ a * Y * Z ^ (s - 1 - a)) ^ 2 ∧
    2 * ∑ a ∈ Finset.range s, LowRankMEG.frobNorm (Z ^ a * Y * Z ^ (s - 1 - a)) ^ 2 ≤
      2 * (s : ℝ) * (Z ^ (2 * s) * J ^ 2).trace ∧
    |iteratedDeriv 3 g 0| ≤ 20 * (s : ℝ) * LiqPremiaEq.opNorm J * iteratedDeriv 2 g 0 := by sorry

end MatrixLeeSidford
