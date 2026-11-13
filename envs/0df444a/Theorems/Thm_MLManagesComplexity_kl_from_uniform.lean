-- Prove2me | Theorems.Thm_MLManagesComplexity_kl_from_uniform
-- name    : MLManagesComplexity.kl_from_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:40:41.404351+00:00
-- url     : https://prove2.me/theorems/97882591-c4a6-4b8d-bd25-f0e386e47200
-- title:
--   Proof of Theorem 6.3 — $\mathrm{KL}(U\|\mu)=\mathbb E_{x\sim U}[\log(1/\mu(x))]-n$
-- statement:
--   For every distribution $\mu$ on $\{0,1\}^n$, with $U_n$ the uniform distribution and logarithms base 2,
--
--   $$
--   \mathrm{KL}(U_n\|\mu)\ =\ \mathbb E_{x\sim U_n}\Bigl[\log\frac1{\mu(x)}\Bigr]-n ,
--   $$
--
--   both sides being $+\infty$ when $\mu$ gives probability $0$ to some string.
--
--   This is the cross-entropy decomposition for the uniform distribution, whose entropy is $n$; it is the last step of the proof of Theorem 6.3.
--
--   Differences from the source:
--   - generalization: µ the P/poly-computable model with polynomially-bounded max-entropy of Theorem 6.3 → µ any distribution on {0,1}^n; reason: the identity uses nothing about µ (if µ misses a point both sides are +∞); the source's µ is a special case
--   - encoding: KL-divergence and cross-entropy (possibly infinite, p.5: "even infinite if for some x, τ(x) > µ(x) = 0") → the published `klBits`/`crossEntropy` in `EReal`, `⊤` exactly on a support mismatch, logarithms base 2; reason: Lean convention; same values
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.3, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_MLManagesComplexity_lexCDF

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- **KL from uniform** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Proof of Theorem 6.3, printed p.11, PDF p.12: "KL(U‖μ) =
E_{x∼U}[log(1/μ(x))] − n"). For every distribution `μ` on `{0,1}^n`, the KL divergence of the
uniform `U` from `μ` equals the cross-entropy of `U` under `μ` minus `n` (bits).

**Formalization Note** In `EReal`; when `μ` misses a point both sides are `⊤`. -/
theorem kl_from_uniform {n : ℕ} (μ : PMF (Fin n → Bool)) :
    klBits (uniformFamily n) μ = crossEntropy (uniformFamily n) μ - (n : EReal) := by sorry

end MLManagesComplexity
