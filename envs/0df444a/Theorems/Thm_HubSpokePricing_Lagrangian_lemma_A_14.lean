-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_lemma_A_14
-- name    : HubSpokePricing.Lagrangian.lemma_A_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:30.561512+00:00
-- url     : https://prove2.me/theorems/a84af385-157c-44cf-b0b9-a9bc3ed32751
-- title:
--   Lemma A.14, p. 54 — a discrete log-concave X with mean µ has E[z^X] ≤ 1/(1 − µ(z − 1)) for 1 ≤ z < 1 + 1/µ
-- statement:
--   Let $X$ be a random variable on $\{0,1,2,\dots\}$ with a discrete log-concave law $p$ (Definition B.1), and let $\mu=\mathbb E[X]=\sum_k k\,p_k$. Then for every $z$ with $1\le z<1+1/\mu$, the generating function $\mathbb E[z^X]=\sum_k p_k z^k$ converges and
--   $$\mathbb E\big[z^X\big]\;\le\;\frac{1}{1-\mu(z-1)}.$$
--
--   The right side is the generating function of the geometric distribution with mean $\mu$: among log-concave laws with a given mean, the geometric one has the largest generating function. This gives the moment-generating-function bound behind Lemma A.12.
--
--   **Formalization Note** The range $1\le z<1+1/\mu$ is written as $1\le z$ and $\mu(z-1)<1$, which is the same range for $\mu>0$ and allows every $z\ge1$ when $\mu=0$ (then $X=0$ almost surely and both sides equal $1$); this avoids Lean's convention $1/0=0$.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 54, Lemma A.14

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Prob

namespace HubSpokePricing.Lagrangian

/-- Lemma A.14 (p. 54): a discrete log-concave `X` with mean `μ` satisfies
`𝔼[z^X] ≤ 1/(1 − μ(z − 1))` for `1 ≤ z < 1 + 1/μ` (every `z ≥ 1` when `μ = 0`). -/
theorem lemma_A_14 (p : ℕ → ℝ) (hp : IsLogConcave p) (z : ℝ) (hz1 : 1 ≤ z)
    (hz : pmfMean p * (z - 1) < 1) :
    Summable (fun k : ℕ => p k * z ^ k) ∧
      ∑' k : ℕ, p k * z ^ k ≤ 1 / (1 - pmfMean p * (z - 1)) := by sorry

end HubSpokePricing.Lagrangian
