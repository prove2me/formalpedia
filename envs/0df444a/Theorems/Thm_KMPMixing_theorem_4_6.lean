-- Prove2me | Theorems.Thm_KMPMixing_theorem_4_6
-- name    : KMPMixing.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:20.938755+00:00
-- url     : https://prove2.me/theorems/d1eb2234-c802-4dea-a113-3e6f6b63680d
-- title:
--   Theorem 4.6 — $\|M^k_{\mathrm{LKMP}}(x^{(0)},\cdot)-\pi_{\mathrm{LKMP}}\|_{\mathrm{TV}}\le 2t\,d^{5/4}\lambda_2^{k/2}$
-- statement:
--   Let $t,k$ be positive integers and $G=(V=[d],E)$ a connected graph on $d\ge2$ vertices. Let $\lambda_2$ be the second largest eigenvalue in absolute value of the two-particle labeled chain $M^{(2,G)}_{\mathrm{LKMP}}$. Then for every initial state $x^{(0)}\in\Omega_G$,
--   $$
--   \big\|M^k_{\mathrm{LKMP}}(x^{(0)},\cdot)-\pi_{\mathrm{LKMP}}\big\|_{\mathrm{TV}}\le2t\cdot d^{5/4}\cdot\lambda_2^{k/2}.
--   $$
--
--   The contraction rate of the $t$-particle labeled chain is governed by the two-particle chain, with only a polynomial prefactor in $t$ and $d$.
--
--   Differences from the source:
--   - encoding: positive integer $d$ → $d\ge2$; reason: with $d=1$ there is no edge and the chain of Definition 4.2 is not defined
--   - encoding: "second largest eigenvalue in absolute value" → `MarkovMixing.lambdaStar` (largest $|\lambda|$ over eigenvalues $\lambda\ne1$); reason: eigenvalue $1$ is simple for this irreducible chain (Lemma 3.4), so the two agree
-- source:
--   Chen et al., arXiv:2609.38044, Theorem 4.6, pp.21–22 (PDF pp.23–24)

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
open MarkovMixing

namespace KMPMixing

/-- **Theorem 4.6** (arXiv:2609.38044, pp.21–22 (PDF pp.23–24)). For positive integers `t`, `d`,
`k`, let `G = ([d], E)` be a connected graph on `d` vertices. For every initial state
`x^{(0)} ∈ Ω_G`,
`‖M^k_LKMP(x^{(0)}, ·) − π_LKMP‖_TV ≤ 2t · d^{5/4} · λ₂^{k/2}`,
where `λ₂` is the second largest eigenvalue in absolute value of `M^{(2,G)}_LKMP`.

**Formalization Note** `λ₂` is `MarkovMixing.lambdaStar` of the two-particle labeled chain (the
largest `|λ|` over eigenvalues `λ ≠ 1`; eigenvalue `1` is simple by Lemma 3.4). `λ₂ ≥ 0`, and
`d^{5/4}`, `λ₂^{k/2}` are real powers. `d ≥ 2` (a graph with an edge) replaces "positive `d`". -/
theorem theorem_4_6 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) (t : ℕ) (ht : 0 < t) (k : ℕ) (hk : 0 < k) (x₀ : Fin t → Fin d) :
    tvDist (rowDist (labeledChain G t) k x₀) (labeledStationary d t) ≤
      2 * (t : ℝ) * (d : ℝ) ^ ((5 : ℝ) / 4) *
        lambdaStar (labeledChain G 2) ^ ((k : ℝ) / 2) := by sorry

end KMPMixing
