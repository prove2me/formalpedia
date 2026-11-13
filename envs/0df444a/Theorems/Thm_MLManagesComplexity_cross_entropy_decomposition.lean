-- Prove2me | Theorems.Thm_MLManagesComplexity_cross_entropy_decomposition
-- name    : MLManagesComplexity.cross_entropy_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:39:18.400192+00:00
-- url     : https://prove2.me/theorems/e8970ae4-2737-4a0f-80fb-3e202bc1d5a2
-- title:
--   §3.2 — cross-entropy decomposition $\mathrm{KL}(\tau\|\mu)=\mathbb E_{x\sim\tau}[\log(1/\mu(x))]-H(\tau)$
-- statement:
--   Let $\tau$ and $\mu$ be probability distributions on a finite set $\Omega$. Write $\mathrm{KL}(\tau\|\mu)=\mathbb E_{x\sim\tau}[\log_2(\tau(x)/\mu(x))]$ for the Kullback–Leibler divergence, $\mathbb E_{x\sim\tau}[\log_2(1/\mu(x))]$ for the cross-entropy, and $H(\tau)=\sum_x\tau(x)\log_2(1/\tau(x))$ for the Shannon entropy, the divergence and the cross-entropy being $+\infty$ when some $x$ has $\tau(x)>0=\mu(x)$. Then
--
--   $$
--   \mathrm{KL}(\tau\|\mu)=\mathbb E_{x\sim\tau}\Bigl[\log\frac{1}{\mu(x)}\Bigr]-H(\tau).
--   $$
--
--   The decomposition explains why minimising $\mathrm{KL}(D\|\mu)$ over models $\mu$ is the same as minimising the cross-entropy (the training loss): $H(D)$ does not depend on $\mu$.
--
--   **Formalization Note** The identity is stated in the extended reals, so the infinite case $+\infty=+\infty-H(\tau)$ is included.
--
--   Differences from the source:
--   - generalization: distributions over {0,1}^n → distributions on an arbitrary finite type Ω; reason: the identity holds on every finite set; Ω = {0,1}^n is the source's case
--   - encoding: KL-divergence and cross-entropy (possibly infinite, p.5: "even infinite if for some x, τ(x) > µ(x) = 0") → the published `klBits`/`crossEntropy` in `EReal`, `⊤` exactly on a support mismatch, logarithms base 2; reason: Lean convention; same values
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2, cross-entropy decomposition, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Information

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- **Cross-entropy decomposition** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2, printed p.4, PDF p.5: "KL(τ‖μ) =
E_{x∼τ}[log(1/μ(x))] − H(τ)"). For distributions `τ, μ` on a finite set, the KL divergence of
`τ` from `μ` equals the cross-entropy of `τ` under `μ` minus the Shannon entropy of `τ`, in bits.

**Formalization Note** `klBits`, `crossEntropy` and `entropy` are the published
`AutoregressiveCompression.Main` ones (base 2; `klBits` and `crossEntropy` are `⊤` exactly when
some `x` has `τ(x) > 0 = μ(x)`). The identity is in `EReal`, so the infinite case
(`⊤ = ⊤ − H(τ)`) is included. -/
theorem cross_entropy_decomposition {Ω : Type} [Fintype Ω] (τ μ : PMF Ω) :
    klBits τ μ = crossEntropy τ μ - (entropy τ : EReal) := by sorry

end MLManagesComplexity
