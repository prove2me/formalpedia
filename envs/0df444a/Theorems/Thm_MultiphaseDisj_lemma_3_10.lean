-- Prove2me | Theorems.Thm_MultiphaseDisj_lemma_3_10
-- name    : MultiphaseDisj.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:55.415062+00:00
-- url     : https://prove2.me/theorems/3cc1d9dc-48d1-4996-b208-c610474888cd
-- title:
--   Lemma 3.10 — a monochromatic near-rectangle
-- statement:
--   Assume the standing hypotheses of §3, fix $i\in I$, and let $G$ be any protocol for epoch $i$ with the properties of Theorem 3.3(a)–(c),(e), with any finite law of $R_{\mathrm{Bob}}$ independent of $(\vec S,X)$ and $Q$. If $\rho_1\ge n^{-1/6}$ (so in particular $\rho_1>0$), then there are a value $(z,1)$ of $Z$, attained with positive probability, and a set $E\subseteq\binom{B_i}{s_i}$ with $\Pr[S_Q^{(i)}\in E\mid Z=(z,1)]\ge3/4$ such that, writing $\mathcal E$ for the event that $Z=(z,1)$ and $S_Q^{(i)}\in E$, and $\varepsilon=1/40$:
--
--   1. (i) $H_\infty(S_Q^{(i)}\mid\mathcal E)\ge\log\binom{n_i}{s_i}-\varepsilon s_i/2$ and $H_\infty(X^{(i)}\mid\mathcal E)\ge\log\binom{n_i}{s_i}-\varepsilon s_i/2$;
--   2. (ii) $I(S_Q^{(i)};X^{(i)}\mid\mathcal E)\le n^{-1/5}$.
--
--   In particular, the distribution of $(S_Q^{(i)},X^{(i)})$ given $\mathcal E$ is a monochromatic $(\varepsilon s_i/2,\,n^{-1/5})$-near-rectangle on $\binom{B_i}{s_i}\times\binom{B_i}{s_i}$.
--
--   This combines Propositions 3.7–3.9 into a single conditioned distribution that is supported on disjoint pairs, by zero error, yet has nearly full min-entropy on both sides and small mutual information.
--
--   Differences from the source:
--   - reading: standing assumptions of §3 (w = Θ(log n), tu w ≤ n^{1/95}, tq ≤ log² n, tu, tq ≥ 1, n sufficiently large) → hypotheses: ∀ 0 < c₁ ≤ c₂, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, 1 ≤ tu, 1 ≤ tq, tu w ≤ n^{1/95}, tq ≤ (log₂ n)²; reason: §3.1 Setup, p.16, and §2.1 'state asymptotic bounds for sufficiently large instances'
--   - generalization: the protocol Gᵢ of Theorem 3.3 (with R_Bob the Bernoulli(p) bits) → every protocol with the properties of Theorem 3.3(a)–(c), the argument structure (e), and any finite law of R_Bob independent of (S⃗, X) and Q; reason: the proof (p.19: 'By Theorem 3.3(e), Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)') uses only these properties; Theorem 3.3 shows Gᵢ is such a protocol
--   - encoding: H, I, H∞ and log with base 2 (§2.2) → entropy, mutual information and min-entropy in bits on finite sample spaces with real point masses; reason: same quantities
--   - reading: 'a value (z, 1) of Z' → a value with Pr[Z = (z, 1)] > 0, stated in the conclusion; reason: a value of a random variable is one it takes; conditioning on it must be defined
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Lemma 3.10, pp.22–23

import Mathlib
import Definitions.Def_MultiphaseDisj_Protocol
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Lemma 3.10 (A monochromatic near-rectangle)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Lemma 3.10, pp.22–23). If
`ρ₁ ≥ n^{−1/6}`, then there are a value `(z, 1)` of `Z` and a set `E ⊆ (Bᵢ choose sᵢ)` with
`Pr[S_Q^{(i)} ∈ E | Z = (z, 1)] ≥ 3/4` such that, writing `𝓔` for the event that `Z = (z, 1)` and
`S_Q^{(i)} ∈ E`,

* (i) `H∞(S_Q^{(i)} | 𝓔) ≥ log (nᵢ choose sᵢ) − ε sᵢ/2` and
  `H∞(X^{(i)} | 𝓔) ≥ log (nᵢ choose sᵢ) − ε sᵢ/2`, and
* (ii) `I(S_Q^{(i)}; X^{(i)} | 𝓔) ≤ n^{−1/5}`.

In particular, the distribution of `(S_Q^{(i)}, X^{(i)})` given `𝓔` is a monochromatic
`(ε sᵢ/2, n^{−1/5})`-near-rectangle on `(Bᵢ choose sᵢ) × (Bᵢ choose sᵢ)`.

**Formalization Note** Stated for every protocol with the properties of Theorem 3.3(a)–(c),(e)
(`Protocol.IsSimProtocol` and the argument structure of `Protocol`), for any finite law of Bob's
randomness `R_Bob` independent of `(S⃗, X)` and `Q`: the proof (§3.3, p.19: "By Theorem 3.3(e),
Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)") uses only these properties.
The standing assumptions of §3 (p.16) are hypotheses: `c₁ log n ≤ w ≤ c₂ log n` for arbitrary
`0 < c₁ ≤ c₂`, `n ≥ n₀(c₁, c₂)`, `tu, tq ≥ 1`, `tu w ≤ n^{1/95}`, `tq ≤ log₂² n`, `i ∈ I`, and
`ρ₁ > 0` (p.19: "Fix i ∈ I with ρ1 > 0"), which here follows from `ρ₁ ≥ n^{−1/6}`. `Pr_{z∼Z_alice|B_Q=1}` and `E_{z∼Z_alice|B_Q=1}` are
taken over the sample space conditioned on `B_Q = 1`, so every value `z` that occurs has
`Pr[Z = (z, 1)] > 0`. Logarithms, entropies and informations are in bits; `ε = 1/40`. The value `(z, 1)` is attained: `Pr[Z = (z, 1)] > 0` is part of the conclusion. -/
theorem lemma_3_10 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ (tu : ℕ) (tq : ℝ), 1 ≤ tu → 1 ≤ tq →
      ((tu * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 95) → tq ≤ (Real.logb 2 n) ^ 2 →
      ∀ i ∈ epochSet n (tu * w),
      ∀ (R : Type) [Fintype R] (rlaw : R → ℝ), IsDist rlaw →
      ∀ (UT PT AT : Type) (G : Protocol n R UT PT AT), G.IsSimProtocol rlaw w tu tq i →
      (n : ℝ) ^ (-(1 : ℝ) / 6) ≤ G.rho1 (tu * w) rlaw (block n (tu * w) i) →
      ∃ (z : (Finset (Fin n) × PT) × (Fin n → AT) × Fin n × (Fin n → Option (Finset (Fin n))))
        (E : Finset (Finset (Fin n))),
        E ⊆ Finset.powersetCard (setSize (tu * w) i) (block n (tu * w) i) ∧
        0 < pr (jointLaw n (tu * w) rlaw) (G.zEvent (block n (tu * w) i) z) ∧
        (3 : ℝ) / 4 ≤ pr (cond (jointLaw n (tu * w) rlaw) (G.zEvent (block n (tu * w) i) z))
          (fun ω => Protocol.sQi (block n (tu * w) i) ω ∈ E) ∧
        -- (i)
        Real.logb 2 ((blockSize n (tu * w) i).choose (setSize (tu * w) i) : ℝ) -
            (1 / 40 : ℝ) * setSize (tu * w) i / 2 ≤
          minEntropy (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
              G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
            (Protocol.sQi (block n (tu * w) i))) ∧
        Real.logb 2 ((blockSize n (tu * w) i).choose (setSize (tu * w) i) : ℝ) -
            (1 / 40 : ℝ) * setSize (tu * w) i / 2 ≤
          minEntropy (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
              G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
            (Protocol.xi (block n (tu * w) i))) ∧
        -- (ii)
        mutualInfo (cond (jointLaw n (tu * w) rlaw) (fun ω =>
              G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
            (Protocol.sQi (block n (tu * w) i)) (Protocol.xi (block n (tu * w) i)) ≤
          (n : ℝ) ^ (-(1 : ℝ) / 5) ∧
        -- in particular
        IsNearRect (Finset.powersetCard (setSize (tu * w) i) (block n (tu * w) i))
            ((1 / 40 : ℝ) * setSize (tu * w) i / 2) ((n : ℝ) ^ (-(1 : ℝ) / 5))
            (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
                G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
              (fun ω => (Protocol.sQi (block n (tu * w) i) ω, Protocol.xi (block n (tu * w) i) ω))) ∧
          IsMono 0
            (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
                G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
              (fun ω => (Protocol.sQi (block n (tu * w) i) ω, Protocol.xi (block n (tu * w) i) ω)))
      := by sorry

end MultiphaseDisj
