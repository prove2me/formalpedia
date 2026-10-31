-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_eq_2_50
-- name    : FuchsThesis.HonestExpert.eq_2_50
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:27.531169+00:00
-- url     : https://prove2.me/theorems/0831441f-47c7-434d-b666-01ccd23a00d3
-- title:
--   (2.50) — the honest-expert inequality on two outcomes
-- statement:
--   Let $n \ge 3$ and let $F_1, \dots, F_n$ be payoff functions that keep the expert honest (for all strictly positive $n$-point distributions). Fix two distinct outcomes $i \ne j$ and real numbers $p, q, r$ with
--
--   $$0 < p < r, \qquad 0 < q < r, \qquad r < 1 .$$
--
--   Then
--
--   $$p\,F_i(q) + (r - p)\,F_j(r - q) \;\le\; p\,F_i(p) + (r - p)\,F_j(r - p) .$$
--
--   This is the honest-expert inequality restricted to distributions that agree off the outcomes $i, j$: the true distribution puts mass $p$ and $r - p$ on $i$ and $j$, the report $q$ and $r - q$, and the remaining mass $1 - r > 0$ is shared identically, so that all other terms cancel. Because $n \ge 3$, the total $r$ on the two outcomes can be any number below $1$. It is the starting point of the "only if" half of Theorem 2.3.
--
--   Differences from the source:
--   - generalization: the outcomes 1 and 2 → any two distinct outcomes i ≠ j; reason: p.24 runs the same argument for the pair (1, k); taking i = 1, j = 2 gives the printed (2.50)
--   - reading: (2.45) for all n-point distributions, payoffs on [0, 1] → (2.45) for all strictly positive n-point distributions; reason: the theorem's logarithmic payoff is undefined at 0 (see Theorem 2.3); the hypothesis is weaker, so the statement covers the source's case
--   - encoding: outcomes 1, …, n → Fin n; reason: Lean indexing
--   - encoding: real payoffs F_k defined on [0, 1] → real functions F_k defined on all of ℝ; reason: only values on (0, 1) enter (the coordinates of strictly positive distributions for n ≥ 3); any F_k on [0, 1] extends to ℝ and the extension changes no clause
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, eq. (2.50), p.21 (PDF p.30)

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace FuchsThesis.HonestExpert

/-- **(2.50): the honest-expert inequality restricted to two outcomes.**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, eq. (2.50), p.21 (PDF p.30): with `q_i = p_i` for `i ≥ 3`, `p₁ = p`, `q₁ = q` and
`r = p + p₂ = q + q₂ < 1`, (2.45) reduces to
`p F₁(q) + (r − p) F₂(r − q) ≤ p F₁(p) + (r − p) F₂(r − p)`.

For `n ≥ 3`, payoffs `F` keeping the expert honest, two distinct outcomes `i ≠ j` (the page's
`1, 2`), and reals `0 < p, q < r < 1`:
`p F_i(q) + (r − p) F_j(r − q) ≤ p F_i(p) + (r − p) F_j(r − p)`.

**Formalization Note.** The page takes the outcomes `1, 2`; any two distinct outcomes are allowed
here (p.24: "Running through the same argument but assuming `q_i = p_i` for all `i` except `i = 1`
and `i = k`"). The constraints `0 < p, q`, `p, q < r < 1` are exactly those making
`p, r − p, q, r − q` and the common remaining mass `1 − r` positive. -/
theorem eq_2_50 {n : ℕ} (hn : 3 ≤ n) {F : Fin n → ℝ → ℝ} (hF : KeepsHonest F)
    {i j : Fin n} (hij : i ≠ j) {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hpr : p < r)
    (hqr : q < r) (hr : r < 1) :
    p * F i q + (r - p) * F j (r - q) ≤ p * F i p + (r - p) * F j (r - p) := by sorry

end FuchsThesis.HonestExpert
