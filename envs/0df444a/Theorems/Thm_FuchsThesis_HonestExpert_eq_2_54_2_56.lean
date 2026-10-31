-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_eq_2_54_2_56
-- name    : FuchsThesis.HonestExpert.eq_2_54_2_56
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:36.548664+00:00
-- url     : https://prove2.me/theorems/e3532232-f448-427e-adfc-72c737478381
-- title:
--   (2.54)–(2.56) — honest payoffs are monotonically nondecreasing
-- statement:
--   Let $n \ge 3$ and let $F_1, \dots, F_n$ keep the expert honest. Then every $F_k$ is monotonically nondecreasing on the open unit interval: for all $k$ and all $p, q$,
--
--   $$0 < q \le p < 1 \;\Longrightarrow\; F_k(q) \le F_k(p) .$$
--
--   In the thesis this is derived from (2.50) by combining it with the inequality obtained by interchanging $p$ and $q$, giving $r(p - q)[F_1(p) - F_1(q)] \ge 0$ (2.54) and the analogous (2.56) for $F_2$. Monotonicity is what later lets Lebesgue's theorem (Lemma 2.1) supply points of differentiability, and it forces the coefficient $\alpha$ of the logarithm to be nonnegative.
--
--   Differences from the source:
--   - generalization: F₁ and F₂ are monotonically nondecreasing → every F_k is; reason: p.24 runs the argument for every pair (1, k); restricting to k = 1, 2 gives the page's claim
--   - reading: (2.45) for all n-point distributions, payoffs on [0, 1] → (2.45) for all strictly positive n-point distributions, monotonicity on (0, 1); reason: under the positivity reading of Theorem 2.3 the values F_k(0), F_k(1) never enter the hypothesis, and (0, 1) is the range of the coordinates for n ≥ 3
--   - encoding: outcomes 1, …, n → Fin n; reason: Lean indexing
--   - encoding: real payoffs F_k defined on [0, 1] → real functions F_k defined on all of ℝ; reason: only values on (0, 1) enter (the coordinates of strictly positive distributions for n ≥ 3); any F_k on [0, 1] extends to ℝ and the extension changes no clause
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, eqs. (2.54)–(2.56), p.22 (PDF p.31)

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace FuchsThesis.HonestExpert

/-- **(2.54)–(2.56): honest payoffs are monotonically nondecreasing.**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, eqs. (2.54)–(2.56), p.22 (PDF p.31): from `r (p − q) [F₁(p) − F₁(q)] ≥ 0` (2.54) "It follows
that F₁ is a monotonically nondecreasing function", and from (2.56) "Therefore, F₂ must also be a
monotonically nondecreasing function."

For `n ≥ 3` and payoffs `F` keeping the expert honest, every `F_k` is monotonically nondecreasing on
the open unit interval `(0, 1)`.

**Formalization Note.** The page proves the claim for `F₁` and `F₂`; by p.24 the same argument
applies to any pair of outcomes, so it is stated for every `k`. `(0, 1)` is the set of values a
coordinate of a strictly positive `n`-point distribution can take when `n ≥ 3`. -/
theorem eq_2_54_2_56 {n : ℕ} (hn : 3 ≤ n) {F : Fin n → ℝ → ℝ} (hF : KeepsHonest F) (k : Fin n) :
    MonotoneOn (F k) (Set.Ioo 0 1) := by sorry

end FuchsThesis.HonestExpert
