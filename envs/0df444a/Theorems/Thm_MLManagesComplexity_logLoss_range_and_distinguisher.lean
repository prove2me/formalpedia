-- Prove2me | Theorems.Thm_MLManagesComplexity_logLoss_range_and_distinguisher
-- name    : MLManagesComplexity.logLoss_range_and_distinguisher
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:42:44.989897+00:00
-- url     : https://prove2.me/theorems/304068f2-0d14-4b17-9af8-640694fba93d
-- title:
--   Proof of Theorem 6.1 — $0\le g\le n^c$ and the distinguisher accepting with probability $\approx g(x)/n^c$
-- statement:
--   Let $\mu=(\mu_n)$ be a P/poly-computable family of distributions on $\{0,1\}^n$ with polynomially-bounded max-entropy, and $g(x)=\log_2(1/\mu_n(x))$. There is one constant $c$ such that
--
--   1. $0\le g(x)\le (n+2)^c$ for every $n$ and every $x\in\{0,1\}^n$; and
--   2. there is a polynomial-size family $A=(A_n)$ of probabilistic circuits that on input $x$ outputs $1$ with probability within $2^{-n}$ of $g(x)/(n+2)^c$:
--
--   $$
--   \Bigl|\Pr[A_n(x)=1]-\frac{g(x)}{(n+2)^c}\Bigr|\ \le\ 2^{-n}\qquad\text{for all } n,\ x\in\{0,1\}^n .
--   $$
--
--   The algorithm $A$ is the distinguisher of the proof of Theorem 6.1: its acceptance probability is an affine image of the log-loss, so any gap in expected log-loss between two distributions becomes a gap in acceptance probability.
--
--   Differences from the source:
--   - encoding: distributions and quantities on {0,1}^n, with "negligible in n" and polynomial bounds understood asymptotically → families indexed by n (`DistFamily := (n : ℕ) → PMF (Fin n → Bool)`), strings as `Fin n → Bool`, bit x_i = `x ⟨i−1,_⟩`; reason: asymptotic statements are about families; the same instances
--   - encoding: 0 ≤ g(x) ≤ n^c and acceptance probability g(x)/n^c → 0 ≤ g(x) ≤ (n+2)^c and acceptance probability ≈ g(x)/(n+2)^c, with the same c; reason: (n+2)^c describes the same polynomial bounds; n^c ≤ 1 cannot bound g at n ≤ 1
--   - encoding: circuits with at most n^c gates (P/poly) → well-formed circuits of size (inputs + gates) at most (n+2)^c; reason: both describe all polynomial bounds; n^c is 0 or 1 at n ≤ 1
--   - generalization: polynomially-bounded max-entropy: µ(x) ≥ 2^{−n^k} for some k → µ_n(x) ≥ 2^{−(n+2)^k} for some k; reason: the source's bound implies this one, so every µ the source allows is allowed; the literal bound at n = 1 would force µ_1 uniform
--   - reading: "P/poly algorithm" distinguishers (Theorem 6.1; §3.3 says "probabilistic P/poly algorithms") → polynomial-size families of probabilistic Boolean circuits, coin inputs counted in the size; reason: §3.3 and the proof of Theorem 6.1 (A outputs 1 with probability g(x)/n^c) use probabilistic algorithms; for nonuniform families fixing the best coins gives a deterministic family of no larger size, so the two readings define the same notion
--   - encoding: "A actually uses an n-bit approximation of g(x)/n^c, which changes each probability below by at most 2^{−n}" → |Pr[A_n(x) = 1] − g(x)/(n+2)^c| ≤ 2^{−n} for every x; reason: the page's parenthetical, stated as the property it gives
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.1, pp.10–11 (PDF pp.11–12)

import Mathlib
import Definitions.Def_MLManagesComplexity_PPolyComputable
import Definitions.Def_MLManagesComplexity_PolyMaxEntropy
import Definitions.Def_MLManagesComplexity_CompIndist

set_option autoImplicit false

open PPADSIS.SubexpSIS

namespace MLManagesComplexity

/-- **The range of g and the distinguisher A** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.1, printed
pp.10–11, PDF pp.11–12: "Since μ has polynomially-bounded max-entropy, there is some c such that
0 ≤ g(x) ≤ n^c for all x ∈ {0, 1}^n. […] Consider the P/poly algorithm A that on input x outputs 1
with probability g(x)/n^c ∈ [0, 1]. (Since g(x) can be irrational, A actually uses an n-bit
approximation of g(x)/n^c, which changes each probability below by at most 2^{−n} and does not
affect the argument.)"). If `μ` is P/poly-computable with polynomially-bounded max-entropy, there
is one exponent `c` such that `0 ≤ g(x) ≤ (n+2)^c` for all `n` and `x ∈ {0,1}^n`, and a
polynomial-size family of probabilistic circuits `Aₙ` whose acceptance probability on every `x`
is within `2^{−n}` of `g(x)/(n+2)^c`.

**Formalization Note** `n^c` becomes `(n+2)^c` (at `n ≤ 1`, `n^c ≤ 1` cannot bound `g`). The same
`c` appears in the range bound and in the scaling of `A`. -/
theorem logLoss_range_and_distinguisher (μ : DistFamily) (hμ : PPolyComputable μ)
    (hmax : PolyMaxEntropy μ) :
    ∃ c : ℕ,
      (∀ (n : ℕ) (x : Fin n → Bool),
        0 ≤ logLoss μ n x ∧ logLoss μ n x ≤ ((n : ℝ) + 2) ^ c) ∧
      ∃ A : ℕ → ProbCircuit, PolySizeDist A ∧
        ∀ (n : ℕ) (x : Fin n → Bool),
          |accept (A n) x - logLoss μ n x / ((n : ℝ) + 2) ^ c| ≤ (2 : ℝ) ^ (-(n : ℝ)) := by sorry

end MLManagesComplexity
