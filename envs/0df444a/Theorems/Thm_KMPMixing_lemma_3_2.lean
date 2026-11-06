-- Prove2me | Theorems.Thm_KMPMixing_lemma_3_2
-- name    : KMPMixing.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:28.611817+00:00
-- url     : https://prove2.me/theorems/1f0238bb-c0db-40ea-b2a9-e14acd155e5e
-- title:
--   Lemma 3.2 — the KMP chain is symmetric, irreducible, aperiodic and reversible for the uniform law
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph on $d\ge2$ vertices and $t$ a positive integer. Then the transition matrix $M=M^{(t,G)}_{\mathrm{KMP}}$ on $\Delta_G$ is a symmetric transition matrix,
--   $$
--   M^\top=M,
--   $$
--   the chain is irreducible and aperiodic, it satisfies detailed balance with respect to the uniform distribution $\pi_{\mathrm{KMP}}$ on $\Delta_G$, $\pi_{\mathrm{KMP}}$ is stationary, and every stationary distribution of $M$ equals $\pi_{\mathrm{KMP}}$.
--
--   These are the basic properties that make $T^{\mathrm{mix}}$ and the spectral quantities of the mission well defined.
--
--   Differences from the source:
--   - encoding: a connected graph $G=(V=[d],E)$ → `G : SimpleGraph (Fin d)` with `G.Connected`, vertex $i$ ↦ index $i-1$; reason: same graphs
--   - encoding: "the KMP chain" (a Markov chain, Definition 3.1) → the explicit clause that $M$ is stochastic; reason: being a transition matrix is part of the source's notion of a Markov chain
-- source:
--   Chen et al., arXiv:2609.38044, Lemma 3.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
open MarkovMixing

namespace KMPMixing

/-- **Lemma 3.2** (Chen, Liu, Qin, Schulman, Song, Yao, Zhao, *A Tale of Two Walks: From Kac to
KMP and Back*, arXiv:2609.38044, p.15 (PDF p.17)). Let `G = ([d], E)` be a connected graph on
`d ≥ 2` vertices and `t` a positive integer. The transition matrix `M^{(t,G)}_KMP` is symmetric.
Moreover, the KMP chain is irreducible, aperiodic, and reversible with respect to the uniform
distribution `π_KMP` on `Δ_G`, which is its unique stationary distribution.

**Formalization Note** "Markov chain" in Definition 3.1 includes that `M` is a transition
matrix; this is the clause `IsStochastic`. Uniqueness is stated over all stationary
distributions. -/
theorem lemma_3_2 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) (t : ℕ) (ht : 0 < t) :
    (kmpChain G t).transpose = kmpChain G t ∧
    IsStochastic (kmpChain G t) ∧
    MarkovMixing.Irreducible (kmpChain G t) ∧
    Aperiodic (kmpChain G t) ∧
    DetailedBalance (kmpChain G t) (uniformDist (State d t)) ∧
    IsStationary (kmpChain G t) (uniformDist (State d t)) ∧
    ∀ μ : State d t → ℝ, IsStationary (kmpChain G t) μ → μ = uniformDist (State d t) := by sorry

end KMPMixing
