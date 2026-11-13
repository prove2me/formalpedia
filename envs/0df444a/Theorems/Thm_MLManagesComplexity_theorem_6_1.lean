-- Prove2me | Theorems.Thm_MLManagesComplexity_theorem_6_1
-- name    : MLManagesComplexity.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:15.784716+00:00
-- url     : https://prove2.me/theorems/0f0f5ca0-3dc8-47f4-8870-571564b9a8b8
-- title:
--   Theorem 6.1 — computationally indistinguishable distributions have negligibly different cross-entropy under every efficient model
-- statement:
--   Let $D=(D_n)$ and $D'=(D'_n)$ be families of distributions on $\{0,1\}^n$ that are computationally indistinguishable: for every polynomial-size family $A$ of probabilistic circuits, $|\Pr_{x\sim D_n}[A_n(x)=1]-\Pr_{x\sim D'_n}[A_n(x)=1]|$ is bounded by a negligible function of $n$. Then for every P/poly-computable family $\mu$ with polynomially-bounded max-entropy there is a negligible function $\nu$ with
--
--   $$
--   \Bigl|\ \mathbb E_{x\sim D_n}\Bigl[\log\frac1{\mu_n(x)}\Bigr]-\mathbb E_{x\sim D'_n}\Bigl[\log\frac1{\mu_n(x)}\Bigr]\ \Bigr|\ \le\ \nu(n)\qquad\text{for every } n .
--   $$
--
--   In words: an efficient model with bounded max-entropy assigns essentially the same cross-entropy (training loss) to any two distributions that efficient observers cannot tell apart, so a learner cannot distinguish pseudorandomness from randomness.
--
--   Differences from the source:
--   - encoding: distributions and quantities on {0,1}^n, with "negligible in n" and polynomial bounds understood asymptotically → families indexed by n (`DistFamily := (n : ℕ) → PMF (Fin n → Bool)`), strings as `Fin n → Bool`, bit x_i = `x ⟨i−1,_⟩`; reason: asymptotic statements are about families; the same instances
--   - encoding: circuits with at most n^c gates (P/poly) → well-formed circuits of size (inputs + gates) at most (n+2)^c; reason: both describe all polynomial bounds; n^c is 0 or 1 at n ≤ 1
--   - generalization: polynomially-bounded max-entropy: µ(x) ≥ 2^{−n^k} for some k → µ_n(x) ≥ 2^{−(n+2)^k} for some k; reason: the source's bound implies this one, so every µ the source allows is allowed; the literal bound at n = 1 would force µ_1 uniform
--   - reading: "P/poly algorithm" distinguishers (Theorem 6.1; §3.3 says "probabilistic P/poly algorithms") → polynomial-size families of probabilistic Boolean circuits, coin inputs counted in the size; reason: §3.3 and the proof of Theorem 6.1 (A outputs 1 with probability g(x)/n^c) use probabilistic algorithms; for nonuniform families fixing the best coins gives a deterministic family of no larger size, so the two readings define the same notion
--   - encoding: "≤ negl(n)" / "is negligible in n" → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n, (quantity at n) ≤ ν n; reason: the source's abuse of notation (§3, p.4); for the nonnegative KL it says exactly that KL is bounded by a negligible function
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem 6.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MLManagesComplexity_PPolyComputable
import Definitions.Def_MLManagesComplexity_PolyMaxEntropy
import Definitions.Def_MLManagesComplexity_CompIndist

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- **Theorem 6.1** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), printed p.10, PDF p.11). Let `D` and `D'` be computationally
indistinguishable families of distributions on `{0,1}^n`. Then for every P/poly-computable family
`μ` with polynomially-bounded max-entropy there is a negligible `ν` with
`|E_{x∼Dₙ}[log₂(1/μₙ(x))] − E_{x∼D'ₙ}[log₂(1/μₙ(x))]| ≤ ν(n)` for every `n`.

**Formalization Note** Distinguishers are polynomial-size probabilistic circuit families
(`CompIndist`); "≤ negl(n)" is "bounded by a negligible function". -/
theorem theorem_6_1 (D D' : DistFamily) (hDD' : CompIndist D D') (μ : DistFamily)
    (hμ : PPolyComputable μ) (hmax : PolyMaxEntropy μ) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ n : ℕ, |expectation (D n) (logLoss μ n) - expectation (D' n) (logLoss μ n)| ≤ ν n := by sorry

end MLManagesComplexity
