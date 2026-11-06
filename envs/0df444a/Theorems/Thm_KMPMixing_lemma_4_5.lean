-- Prove2me | Theorems.Thm_KMPMixing_lemma_4_5
-- name    : KMPMixing.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:38.244844+00:00
-- url     : https://prove2.me/theorems/1906cb93-daba-4653-bceb-64263e4998f7
-- title:
--   Lemma 4.5 — $\pi_{\mathrm{LKMP}}=\mathbb E[(w^{(k)})^{\otimes t}]$ with $w^{(k)}=u\cdot B_k$, $u\sim\mathrm{Dirichlet}(1,\dots,1)$
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph on $d\ge2$ vertices and $t$ a positive integer. Let $k\in\mathbb N$ and let $u$ be drawn from $\mathrm{Dirichlet}(1,\dots,1)$, the uniform law on the simplex $\{u\in\mathbb R^d_{\ge0}:\sum_iu_i=1\}$. Let the edges $\{i_s,j_s\}_{1\le s\le k}$ and parameters $\{p_s\}_{1\le s\le k}$ be as in Observation 4.4 and independent of $u$, and set $w^{(k)}=u\cdot B_k$. Then for every $y\in\Omega_G$,
--   $$
--   \pi_{\mathrm{LKMP}}(y)=\mathbb E_{\{i_s,j_s\},\{p_s\},u}\Big[\prod_{i=1}^tw^{(k)}(y_i)\Big].
--   $$
--
--   The stationary law has the same conditional product structure as the time-$k$ law, which lets the two be compared particle by particle.
--
--   Differences from the source:
--   - encoding: a connected graph $G$ on $d$ vertices, $t$ positive (standing assumptions of Definition 4.2) → hypotheses `G.Connected`, `2 ≤ d`, `0 < t`; reason: with $d=1$ there is no edge and the chain is not defined
--   - encoding: one expectation over $(\{i_s,j_s\},\{p_s\},u)$ → the expectation over $u$ inside the expectation over the edges and parameters; reason: $u$ is independent of them and the integrand is bounded, so the iterated expectation is the joint one
-- source:
--   Chen et al., arXiv:2609.38044, Lemma 4.5, p.20 (PDF p.22); Dirichlet(1,…,1), p.11

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
import Definitions.Def_KMPMixing_auxMatrix
import Definitions.Def_PolyVoting_dirichletMeasure
open MarkovMixing MeasureTheory

namespace KMPMixing

/-- **Lemma 4.5** (arXiv:2609.38044, p.20 (PDF p.22)). Let `k ∈ ℕ` and let `u` be drawn from
`Dirichlet(1, …, 1)`. For random edges `{i_s, j_s}_{1≤s≤k}` and parameters `{p_s}_{1≤s≤k}`
independent of `u`, define `A_s`, `B_s` as in Eqs. (8), (9) and `w^{(k)} = u · B_k`. Then for every
`y ∈ Ω_G`,
`π_LKMP(y) = E_{{i_s,j_s}, {p_s}, u}[∏_{i=1}^t w^{(k)}(y_i)]`.

**Formalization Note** `Dirichlet(1, …, 1)` is `PolyVoting.dirichletMeasure` with all parameters
`1` (the uniform law on the simplex, a probability measure on `Fin d → ℝ`); `u · B_k` is the row
vector `Matrix.vecMul u (B_k)`. The expectation over `u` is taken inside the expectation over the
edges and parameters; the integrand is a bounded polynomial on the simplex. Standing assumptions
of §4 (`G` connected, `d ≥ 2`, `t` positive) are hypotheses. -/
theorem lemma_4_5 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) (t : ℕ) (ht : 0 < t) (k : ℕ) (y : Fin t → Fin d) :
    labeledStationary d t y =
      auxExpect G k (fun es ps =>
        ∫ u, ∏ i, Matrix.vecMul u (auxProd es ps) (y i)
          ∂(PolyVoting.dirichletMeasure (fun _ : Fin d => (1 : ℝ)))) := by sorry

end KMPMixing
