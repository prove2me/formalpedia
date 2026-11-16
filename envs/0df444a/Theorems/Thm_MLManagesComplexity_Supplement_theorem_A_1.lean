-- Prove2me | Theorems.Thm_MLManagesComplexity_Supplement_theorem_A_1
-- name    : MLManagesComplexity.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:07:48.644793+00:00
-- url     : https://prove2.me/theorems/b20dd4f8-d22a-4843-adba-dd9033010bc3
-- title:
--   Theorem A.1 — the CDF $F_\mu$ is polynomial-time computable iff $f_\mu\in\mathrm{FP}$
-- statement:
--   Let $\mu=(\mu_n)_n$ be a family of distributions, $\mu_n$ on $\{0,1\}^n$. The following are equivalent.
--
--   1. The cumulative distribution function $F_{\mu}(x)=\sum_{z\le x}\mu(z)$, with $\le$ the lexicographic order on $\{0,1\}^n$, is computable in polynomial time.
--   2. The conditional probability function
--   $$
--   f_\mu(y)=\Pr_{x\sim\mu}[x_{|y|+1}=1\mid x_{1\dots|y|}=y],\qquad y\in\{0,1\}^{<n},
--   $$
--   with the convention $f_\mu(y)=0$ if $\mu(y0)+\mu(y1)=0$, is in FP.
--
--   Values are rationals represented by numerator and denominator.
--
--   The theorem says that a distribution is efficiently computable in the CDF sense exactly when it is efficiently computable autoregressively, bit by bit; it is how the paper passes between its CDF-based definition of computable distributions and next-bit predictors such as language models.
--
--   **Formalization Note** Both conditions use one polynomial-time machine (published `PolyTimeComputable`) for all lengths $n$; the machine for $f_\mu$ receives $n$ in unary followed by $y$. Rationals are output as their lowest-terms numerator and denominator in binary. No assumption on $\mu$ is added.
--
--   Differences from the source:
--   - reading: a distribution µ on {0,1}^n whose CDF is computable in polynomial time / whose f_µ is in FP → a family (µ_n)_n with one polynomial-time machine for all n in each condition; reason: polynomial time is meaningful only for a family; the paper's asymptotics are over n
--   - encoding: f_µ(y) in FP for prefixes y ∈ {0,1}^{<n} → the machine receives 1^n 0 followed by y; reason: y alone does not determine n; giving n in unary adds only linear input length
--   - encoding: values are rationals represented by numerator and denominator → the output equals encRat q (numerator in lowest terms, then the positive denominator, in self-delimiting binary) with q equal to the value; reason: reducing a fraction takes polynomial time, so no family changes class
--   - encoding: computable in polynomial time / FP → published PolyTimeComputable (Mathlib TM2ComputableInPolyTime on List Bool); reason: standard Turing-machine model of polynomial time
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem A.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MLManagesComplexity_Supplement_CondProbFP

set_option autoImplicit false

namespace MLManagesComplexity.Supplement

/-- **Theorem A.1** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233
(version of 2026-10-31, sha256 4874d83f…), Appendix A, printed p.15, PDF p.16): for a
distribution `µ` on `{0,1}^n`, the following are equivalent: (1) the lexicographic cumulative
distribution function `F_µ(x) = ∑_{z≤x} µ(z)` is computable in polynomial time; (2) the conditional
probability function `f_µ(y) = Pr_{x∼µ}[x_{|y|+1} = 1 | x_{1…|y|} = y]` (with `f_µ(y) = 0` if
`µ(y0) + µ(y1) = 0`) is in FP for all prefixes `y ∈ {0,1}^{<n}`; values are rationals represented
by numerator and denominator.

**Formalization Note** Both conditions are about a family `µ = (µ_n)_n`, with one polynomial-time
machine for all `n`; the machine for `f_µ` receives `n` in unary before `y`. Rationals are output
as `encRat q` (numerator and denominator in binary). No hypothesis on `µ` is added. -/
theorem theorem_A_1 (μ : DistFamily) : CDFPolyTime μ ↔ CondProbFP μ := by sorry

end MLManagesComplexity.Supplement
