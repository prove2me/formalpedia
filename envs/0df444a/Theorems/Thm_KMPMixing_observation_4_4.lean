-- Prove2me | Theorems.Thm_KMPMixing_observation_4_4
-- name    : KMPMixing.observation_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:14.354532+00:00
-- url     : https://prove2.me/theorems/117f8825-cabb-498d-a833-0b4b5dd82c77
-- title:
--   Observation 4.4 — conditional product structure of the labeled chain
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph on $d\ge2$ vertices and $t$ a positive integer. Conditional on the edges $\{i_s,j_s\}_{1\le s\le k}$ and parameters $\{p_s\}_{1\le s\le k}$, a particle started at $i$ has law $q^{(k)}_i=e_iB_k$ after $k$ steps, and the labeled configuration has the product law $\mu_k=\bigotimes_{\ell=1}^tq^{(k)}_{x^{(0)}_\ell}$. Averaging, for every $k\in\mathbb N$ and $x^{(0)},y\in\Omega_G$,
--   $$
--   M^k_{\mathrm{LKMP}}(x^{(0)},y)=\mathbb E_{\{i_s,j_s\},\{p_s\}}\big[\mu_k(y)\big]=\mathbb E_{\{i_s,j_s\},\{p_s\}}\Big[\prod_{\ell=1}^tB_k\big(x^{(0)}_\ell,y_\ell\big)\Big],
--   $$
--   where the edges are i.i.d. uniform on $E$ and the parameters i.i.d. $\mathrm{Unif}[0,1]$, independent of the edges.
--
--   Given the auxiliary randomness, the labeled particles move independently, which reduces the analysis to one particle.
--
--   Differences from the source:
--   - encoding: a connected graph $G$ on $d$ vertices, $t$ positive (standing assumptions of Definition 4.2) → hypotheses `G.Connected`, `2 ≤ d`, `0 < t`; reason: with $d=1$ there is no edge and the chain is not defined
--   - encoding: $\mu_k(y)$ with $q^{(k)}_i=e_iB_k$ → $\prod_\ell B_k(x^{(0)}_\ell,y_\ell)$; reason: $(e_iB_k)(y)=B_k(i,y)$, the same number
-- source:
--   Chen et al., arXiv:2609.38044, Observation 4.4, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
import Definitions.Def_KMPMixing_auxMatrix
open MarkovMixing

namespace KMPMixing

/-- **Observation 4.4** (arXiv:2609.38044, p.20 (PDF p.22)). Conditional on the edges
`{i_s, j_s}_{1≤s≤k}` and the parameters `{p_s}_{1≤s≤k}`, a particle initially at `i` has law
`q_i^{(k)} = e_i · B_k` after `k` steps, and the labeled configuration has the product law
`μ_k = ⊗_{ℓ=1}^t q^{(k)}_{x^{(0)}_ℓ}`. Averaging over the auxiliary randomness, for every
`y ∈ Ω_G`,
`M^k_LKMP(x^{(0)}, y) = E_{{i_s,j_s}, {p_s}}[μ_k(y)] = E[∏_{ℓ=1}^t B_k(x^{(0)}_ℓ, y_ℓ)]`.

**Formalization Note** `μ_k(y) = ∏_ℓ q^{(k)}_{x^{(0)}_ℓ}(y_ℓ) = ∏_ℓ B_k(x^{(0)}_ℓ, y_ℓ)`. The
expectation `auxExpect` takes one independent uniform edge and one independent `Unif[0,1]`
parameter per step. Standing assumptions of §4 (`G` connected, `d ≥ 2`, `t` positive) are
hypotheses. -/
theorem observation_4_4 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) (t : ℕ) (ht : 0 < t) (k : ℕ) (x₀ y : Fin t → Fin d) :
    (labeledChain G t ^ k) x₀ y =
      auxExpect G k (fun es ps => ∏ ℓ, auxProd es ps (x₀ ℓ) (y ℓ)) := by sorry

end KMPMixing
