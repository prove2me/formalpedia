-- Prove2me | Theorems.Thm_KMPMixing_lemma_3_4
-- name    : KMPMixing.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:06.801389+00:00
-- url     : https://prove2.me/theorems/7d152e41-b4ee-424f-8f1e-beaa5fe0722c
-- title:
--   Lemma 3.4 — the labeled KMP chain is reversible for $\pi_{\mathrm{LKMP}}$
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph on $d\ge2$ vertices and $t$ a positive integer. Then $M^{(t,G)}_{\mathrm{LKMP}}$ is a transition matrix on $\Omega_G=[d]^t$, the labeled chain is irreducible and aperiodic,
--   $$
--   \pi_{\mathrm{LKMP}}(x)=\frac{\prod_{i=1}^d\#_i(x)!}{t!\,\binom{t+d-1}{d-1}}
--   $$
--   is a probability distribution on $\Omega_G$, the chain satisfies detailed balance with respect to $\pi_{\mathrm{LKMP}}$, and $\pi_{\mathrm{LKMP}}$ is its unique stationary distribution.
--
--   The labeled chain is the vehicle of the mixing analysis; this lemma identifies its equilibrium.
--
--   Differences from the source:
--   - encoding: a connected graph $G=(V=[d],E)$ → `G : SimpleGraph (Fin d)` with `G.Connected`, vertex $i$ ↦ index $i-1$; reason: same graphs
--   - encoding: "the labeled KMP chain" (a Markov chain, Definition 3.3) → the explicit clause that $M$ is stochastic; reason: being a transition matrix is part of the source's notion of a Markov chain
-- source:
--   Chen et al., arXiv:2609.38044, Lemma 3.4, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
open MarkovMixing

namespace KMPMixing

/-- **Lemma 3.4** (arXiv:2609.38044, p.16 (PDF p.18)). Let `G = ([d], E)` be a connected graph on
`d ≥ 2` vertices and `t` a positive integer. The labeled KMP chain is irreducible and aperiodic.
Moreover, it is reversible with respect to the probability distribution
`π_LKMP(x) = ∏_{i=1}^d #_i(x)! / (t! · C(t + d − 1, d − 1))` on `Ω_G = [d]^t`. In particular,
`π_LKMP` is the unique stationary distribution of `M^{(t,G)}_LKMP`.

**Formalization Note** "Markov chain" in Definition 3.3 includes that `M` is a transition
matrix (clause `IsStochastic`); "probability distribution" is the clause `IsDist`. -/
theorem lemma_3_4 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) (t : ℕ) (ht : 0 < t) :
    IsStochastic (labeledChain G t) ∧
    MarkovMixing.Irreducible (labeledChain G t) ∧
    Aperiodic (labeledChain G t) ∧
    IsDist (labeledStationary d t) ∧
    DetailedBalance (labeledChain G t) (labeledStationary d t) ∧
    IsStationary (labeledChain G t) (labeledStationary d t) ∧
    ∀ μ : (Fin t → Fin d) → ℝ, IsStationary (labeledChain G t) μ → μ = labeledStationary d t := by sorry

end KMPMixing
