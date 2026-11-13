-- Prove2me | Theorems.Thm_MLManagesComplexity_acceptance_gap
-- name    : MLManagesComplexity.acceptance_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:42:28.462118+00:00
-- url     : https://prove2.me/theorems/6168fb93-c41c-42ee-9f5b-9e52807efef1
-- title:
--   Proof of Theorem 6.1 — the acceptance gap equals $(1/n^c)\,|\mathbb E_D[g]-\mathbb E_{D'}[g]|$ up to the approximation error
-- statement:
--   Let $A$ be a probabilistic circuit, $K>0$, $\varepsilon\ge0$, $g:\{0,1\}^n\to\mathbb R$, and $D,D'$ distributions on $\{0,1\}^n$. If $A$ accepts every input with probability within $\varepsilon$ of $g(x)/K$, i.e. $|\Pr[A(x)=1]-g(x)/K|\le\varepsilon$ for all $x$, then
--
--   $$
--   \Bigl|\ \bigl|\Pr_{x\sim D}[A(x)=1]-\Pr_{x\sim D'}[A(x)=1]\bigr|-\frac1K\bigl|\mathbb E_{x\sim D}[g(x)]-\mathbb E_{x\sim D'}[g(x)]\bigr|\ \Bigr|\ \le\ 2\varepsilon .
--   $$
--
--   For $\varepsilon=0$ this is the paper's equality $|\Pr_{x\sim D}[A(x)=1]-\Pr_{x\sim D'}[A(x)=1]|=\frac{1}{n^c}|\mathbb E_{x\sim D}[g(x)]-\mathbb E_{x\sim D'}[g(x)]|$ (with $K=n^c$); the error term accounts for the paper's parenthetical remark that $A$ uses an $n$-bit approximation, which changes each probability by at most $2^{-n}$. This identity turns a gap in expected log-loss into a distinguishing advantage.
--
--   Differences from the source:
--   - generalization: the equality |Pr_D[A=1] − Pr_{D′}[A=1]| = (1/n^c)|E_D[g] − E_{D′}[g]| for A accepting with probability exactly g(x)/n^c (up to the parenthetical's 2^{−n} change) → for any probabilistic circuit, any K > 0 and ε ≥ 0, any real g and any D, D′: if |Pr[A(x)=1] − g(x)/K| ≤ ε for all x then the two sides differ by at most 2ε; reason: ε = 0, K = n^c gives the page's equality; ε = 2^{−n} is the page's parenthetical made explicit
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.1, display, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_MLManagesComplexity_CompIndist

set_option autoImplicit false

open PPADSIS.SubexpSIS AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- **The acceptance gap** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.1, display, printed p.11, PDF p.12:
"|Pr_{x∼D}[A(x) = 1] − Pr_{x∼D′}[A(x) = 1]| = (1/n^c) |E_{x∼D}[g(x)] − E_{x∼D′}[g(x)]|", with the
parenthetical "A actually uses an n-bit approximation of g(x)/n^c, which changes each probability
below by at most 2^{−n}"). Let `A` be a probabilistic circuit, `K > 0`, `ε ≥ 0`, `g` a real function
on `{0,1}^n`, and `D, D'` distributions on `{0,1}^n`. If `A` accepts every `x` with probability
within `ε` of `g(x)/K`, then the distinguishing gap of `A` differs from
`(1/K)|E_D[g] − E_{D'}[g]|` by at most `2ε`.

**Formalization Note** At `ε = 0` this is the page's equality; the error term is the page's
parenthetical made explicit, with `K = n^c` and `ε = 2^{−n}` in the proof. Expectations are the
published finite sums `AutoregressiveCompression.Main.expectation`. -/
theorem acceptance_gap {n : ℕ} (A : ProbCircuit) (K ε : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (g : (Fin n → Bool) → ℝ) (D D' : PMF (Fin n → Bool))
    (hA : ∀ x : Fin n → Bool, |accept A x - g x / K| ≤ ε) :
    abs (|acceptUnder A D - acceptUnder A D'| - (1 / K) * |expectation D g - expectation D' g|)
      ≤ 2 * ε := by sorry

end MLManagesComplexity
