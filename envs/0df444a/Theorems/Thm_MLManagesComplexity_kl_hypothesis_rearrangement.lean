-- Prove2me | Theorems.Thm_MLManagesComplexity_kl_hypothesis_rearrangement
-- name    : MLManagesComplexity.kl_hypothesis_rearrangement
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:40:35.097443+00:00
-- url     : https://prove2.me/theorems/a90ef9e6-94a1-4b81-a0b3-eb486caa7449
-- title:
--   Proof of Theorem 6.3 — $\mathrm{KL}(D\|\mu)\le\mathrm{KL}(D\|U)$ rearranges to $\mathbb E_D[\log(1/\mu)]\le\mathbb E_D[\log(1/U)]=n$
-- statement:
--   Let $D$ and $\mu$ be distributions on $\{0,1\}^n$ and $U_n$ the uniform distribution. If $\mathrm{KL}(D\|\mu)\le\mathrm{KL}(D\|U_n)$, then
--
--   $$
--   \mathbb E_{x\sim D}\Bigl[\log\frac1{\mu(x)}\Bigr]\ \le\ \mathbb E_{x\sim D}\Bigl[\log\frac1{U_n(x)}\Bigr]\ =\ n ,
--   $$
--
--   where cross-entropies are $+\infty$ on a support mismatch and logarithms are base 2.
--
--   This is the step of the proof of Theorem 6.3 that converts the fitting hypothesis into a bound on the model's cross-entropy on the generator's output.
--
--   Differences from the source:
--   - generalization: D the output distribution of a cryptographic PRG and µ the P/poly-computable model with polynomially-bounded max-entropy of Theorem 6.3 → D and µ any distributions on {0,1}^n; reason: the rearrangement uses nothing about D or µ (a µ missing a point of D's support makes KL(D‖µ) = +∞ and the hypothesis false); the source's D and µ are a special case
--   - encoding: KL-divergence and cross-entropy (possibly infinite, p.5: "even infinite if for some x, τ(x) > µ(x) = 0") → the published `klBits`/`crossEntropy` in `EReal`, `⊤` exactly on a support mismatch, logarithms base 2; reason: Lean convention; same values
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.3, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_MLManagesComplexity_lexCDF

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- **The hypothesis rearranged** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.3, printed p.11, PDF p.12: "The
hypothesis KL(D‖μ) ≤ KL(D‖U) rearranges to E_{x∼D}[log(1/μ(x))] ≤ E_{x∼D}[log(1/U(x))] = n.").
For distributions `D, μ` on `{0,1}^n` with `KL(D‖μ) ≤ KL(D‖U)`, the cross-entropy of `D` under `μ`
is at most that under the uniform `U`, and the latter equals `n` (bits).

**Formalization Note** Any `D` (not only a generator's output). `klBits` and `crossEntropy` are the
published base-2 `EReal` quantities of `AutoregressiveCompression.Main`. -/
theorem kl_hypothesis_rearrangement {n : ℕ} (D μ : PMF (Fin n → Bool))
    (h : klBits D μ ≤ klBits D (uniformFamily n)) :
    crossEntropy D μ ≤ crossEntropy D (uniformFamily n) ∧
      crossEntropy D (uniformFamily n) = (n : EReal) := by sorry

end MLManagesComplexity
