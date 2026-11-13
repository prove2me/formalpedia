-- Prove2me | Theorems.Thm_MLManagesComplexity_logLoss_ppoly_computable
-- name    : MLManagesComplexity.logLoss_ppoly_computable
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:42:47.029208+00:00
-- url     : https://prove2.me/theorems/caa01bf8-53ae-4cb0-9ead-a4f29c0c6616
-- title:
--   Proof of Theorem 6.1 — $g=\log(1/\mu)$ is P/poly-computable to any polynomial precision
-- statement:
--   Let $\mu=(\mu_n)$ be a P/poly-computable family of distributions on $\{0,1\}^n$ with polynomially-bounded max-entropy, and let $g(x)=\log_2(1/\mu_n(x))$ for $x\in\{0,1\}^n$. Then $g$ is computable by polynomial-size circuits to any polynomial precision: for every $d$ there is a constant $c$ such that for every $n$ there is a well-formed Boolean circuit $C_n$ with $n$ inputs, size at most $(n+2)^c$, and $2w_n$ outputs, whose output on every $x$ is a numerator $a$ and a nonzero denominator $b$ with
--
--   $$
--   \Bigl|\frac{a}{b}-\log_2\frac{1}{\mu_n(x)}\Bigr|\ \le\ 2^{-(n+2)^d}.
--   $$
--
--   This is the first step of the proof of Theorem 6.1: the log-loss of a computable model is itself efficiently computable, which is what lets a small circuit use it as a distinguisher.
--
--   Differences from the source:
--   - encoding: distributions and quantities on {0,1}^n, with "negligible in n" and polynomial bounds understood asymptotically → families indexed by n (`DistFamily := (n : ℕ) → PMF (Fin n → Bool)`), strings as `Fin n → Bool`, bit x_i = `x ⟨i−1,_⟩`; reason: asymptotic statements are about families; the same instances
--   - encoding: circuits with at most n^c gates (P/poly) → well-formed circuits of size (inputs + gates) at most (n+2)^c; reason: both describe all polynomial bounds; n^c is 0 or 1 at n ≤ 1
--   - generalization: polynomially-bounded max-entropy: µ(x) ≥ 2^{−n^k} for some k → µ_n(x) ≥ 2^{−(n+2)^k} for some k; reason: the source's bound implies this one, so every µ the source allows is allowed; the literal bound at n = 1 would force µ_1 uniform
--   - reading: "Since µ is P/poly-computable, so is g" (a step inside the proof of Theorem 6.1, whose µ has polynomially-bounded max-entropy) → polynomially-bounded max-entropy is a hypothesis; reason: it is the standing hypothesis of the proof; g = log(1/µ) is undefined where µ(x) = 0
--   - encoding: g computable "to any polynomial precision" → for every d, error at most 2^{−(n+2)^d}, output as numerator and nonzero denominator in the format of PPolyComputable; reason: the bounds 2^{−(n+2)^d} cover every 2^{−p(n)} with p a polynomial; same format as the source's computable values (Theorem A.1)
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.1, p.10 (PDF p.11): "so is g, to any polynomial precision"

import Mathlib
import Definitions.Def_MLManagesComplexity_PPolyComputable
import Definitions.Def_MLManagesComplexity_PolyMaxEntropy

set_option autoImplicit false

open PPADSIS.SubexpSIS

namespace MLManagesComplexity

/-- **The log-loss is P/poly-computable to any polynomial precision** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of
Theorem 6.1, printed p.10, PDF p.11: "Let g(x) = log(1/μ(x)). Since μ is P/poly-computable, so is
g, to any polynomial precision."). If `μ` is P/poly-computable and has polynomially-bounded
max-entropy, then for every `d` there is `c` such that for every `n` a well-formed circuit with
`n` inputs and size at most `(n+2)^c` outputs, on every `x`, a rational (numerator and nonzero
denominator) within `2^{−(n+2)^d}` of `g(x) = log₂(1/μₙ(x))`.

**Formalization Note** "Any polynomial precision" is error `2^{−p(n)}` for every polynomial
`p`; the bounds `(n+2)^d` cover all of them. The circuit format is that of `PPolyComputable`. -/
theorem logLoss_ppoly_computable (μ : DistFamily) (hμ : PPolyComputable μ)
    (hmax : PolyMaxEntropy μ) :
    ∀ d : ℕ, ∃ c : ℕ, ∀ n : ℕ, ∃ (C : Circuit) (w : ℕ),
      C.WF ∧ C.nIn = n ∧ C.outs.length = 2 * w ∧ C.size ≤ (n + 2) ^ c ∧
        ∀ x : Fin n → Bool, ratDefined C w x ∧
          |ratOut C w x - logLoss μ n x| ≤ (2 : ℝ) ^ (-(((n : ℝ) + 2) ^ d)) := by sorry

end MLManagesComplexity
