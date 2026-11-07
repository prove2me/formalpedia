-- Prove2me | Theorems.Thm_MultiphaseDisj_corollary_3_11
-- name    : MultiphaseDisj.corollary_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:39.591908+00:00
-- url     : https://prove2.me/theorems/60a8c41e-64ca-4f33-9bde-09f9de6c8295
-- title:
--   Corollary 3.11 — a nearly monochromatic rectangle
-- statement:
--   Assume the standing hypotheses of §3, fix $i\in I$, and let $G$ be any protocol for epoch $i$ with the properties of Theorem 3.3(a)–(c),(e), with any finite law of $R_{\mathrm{Bob}}$ independent of $(\vec S,X)$ and $Q$. If $\rho_1\ge n^{-1/6}$ (so in particular $\rho_1>0$), let $\mathcal E$ be the event of Lemma 3.10. Then
--   $$
--   R:=S_Q^{(i)}\big|_{\mathcal E}\otimes X^{(i)}\big|_{\mathcal E}
--   $$
--   is an $(\varepsilon s_i/2)$-rectangle on $\binom{B_i}{s_i}\times\binom{B_i}{s_i}$ (with $\varepsilon=1/40$), and
--   $$
--   \Pr_{(S,X)\sim R}\big[S\cap X\neq\emptyset\big]\le n^{-1/10}.
--   $$
--
--   Differences from the source:
--   - reading: standing assumptions of §3 (w = Θ(log n), tu w ≤ n^{1/95}, tq ≤ log² n, tu, tq ≥ 1, n sufficiently large) → hypotheses: ∀ 0 < c₁ ≤ c₂, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, 1 ≤ tu, 1 ≤ tq, tu w ≤ n^{1/95}, tq ≤ (log₂ n)²; reason: §3.1 Setup, p.16, and §2.1 'state asymptotic bounds for sufficiently large instances'
--   - generalization: the protocol Gᵢ of Theorem 3.3 (with R_Bob the Bernoulli(p) bits) → every protocol with the properties of Theorem 3.3(a)–(c), the argument structure (e), and any finite law of R_Bob independent of (S⃗, X) and Q; reason: the proof (p.19: 'By Theorem 3.3(e), Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)') uses only these properties; Theorem 3.3 shows Gᵢ is such a protocol
--   - encoding: H, I, H∞ and log with base 2 (§2.2) → entropy, mutual information and min-entropy in bits on finite sample spaces with real point masses; reason: same quantities
--   - reading: 'the event of Lemma 3.10' → every event 𝓔 = {Z = (z,1), S_Q^{(i)} ∈ E} with the properties Lemma 3.10 asserts: E ⊆ (Bᵢ choose sᵢ), Pr[Z = (z,1)] > 0, Pr[S_Q^{(i)} ∈ E | Z = (z,1)] ≥ 3/4, (i) and (ii); reason: the corollary uses only these properties of the event
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Corollary 3.11, p.23

import Mathlib
import Definitions.Def_MultiphaseDisj_Protocol
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Corollary 3.11 (A nearly monochromatic rectangle)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Corollary 3.11, p.23). If
`ρ₁ ≥ n^{−1/6}`, let `𝓔` be the event of Lemma 3.10. Then
`R := S_Q^{(i)}|𝓔 ⊗ X^{(i)}|𝓔` is an `(ε sᵢ/2)`-rectangle on
`(Bᵢ choose sᵢ) × (Bᵢ choose sᵢ)`, and `Pr_{(S,X)∼R}[S ∩ X ≠ ∅] ≤ n^{−1/10}`.

**Formalization Note** Stated for every protocol with the properties of Theorem 3.3(a)–(c),(e)
(`Protocol.IsSimProtocol` and the argument structure of `Protocol`), for any finite law of Bob's
randomness `R_Bob` independent of `(S⃗, X)` and `Q`: the proof (§3.3, p.19: "By Theorem 3.3(e),
Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)") uses only these properties.
The standing assumptions of §3 (p.16) are hypotheses: `c₁ log n ≤ w ≤ c₂ log n` for arbitrary
`0 < c₁ ≤ c₂`, `n ≥ n₀(c₁, c₂)`, `tu, tq ≥ 1`, `tu w ≤ n^{1/95}`, `tq ≤ log₂² n`, `i ∈ I`, and
`ρ₁ > 0` (p.19: "Fix i ∈ I with ρ1 > 0"), which here follows from `ρ₁ ≥ n^{−1/6}`. `Pr_{z∼Z_alice|B_Q=1}` and `E_{z∼Z_alice|B_Q=1}` are
taken over the sample space conditioned on `B_Q = 1`, so every value `z` that occurs has
`Pr[Z = (z, 1)] > 0`. Logarithms, entropies and informations are in bits; `ε = 1/40`. "The event of Lemma 3.10" is any event `𝓔 = {Z = (z, 1), S_Q^{(i)} ∈ E}` with the
properties that Lemma 3.10 asserts: `E ⊆ (Bᵢ choose sᵢ)`, `Pr[Z = (z, 1)] > 0`,
`Pr[S_Q^{(i)} ∈ E | Z = (z, 1)] ≥ 3/4`, (i) and (ii). -/
theorem corollary_3_11 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ (tu : ℕ) (tq : ℝ), 1 ≤ tu → 1 ≤ tq →
      ((tu * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 95) → tq ≤ (Real.logb 2 n) ^ 2 →
      ∀ i ∈ epochSet n (tu * w),
      ∀ (R : Type) [Fintype R] (rlaw : R → ℝ), IsDist rlaw →
      ∀ (UT PT AT : Type) (G : Protocol n R UT PT AT), G.IsSimProtocol rlaw w tu tq i →
      (n : ℝ) ^ (-(1 : ℝ) / 6) ≤ G.rho1 (tu * w) rlaw (block n (tu * w) i) →
      ∀ (z : (Finset (Fin n) × PT) × (Fin n → AT) × Fin n × (Fin n → Option (Finset (Fin n))))
        (E : Finset (Finset (Fin n))),
        E ⊆ Finset.powersetCard (setSize (tu * w) i) (block n (tu * w) i) →
        0 < pr (jointLaw n (tu * w) rlaw) (G.zEvent (block n (tu * w) i) z) →
        (3 : ℝ) / 4 ≤ pr (cond (jointLaw n (tu * w) rlaw) (G.zEvent (block n (tu * w) i) z))
          (fun ω => Protocol.sQi (block n (tu * w) i) ω ∈ E) →
        Real.logb 2 ((blockSize n (tu * w) i).choose (setSize (tu * w) i) : ℝ) -
            (1 / 40 : ℝ) * setSize (tu * w) i / 2 ≤
          minEntropy (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
              G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
            (Protocol.sQi (block n (tu * w) i))) →
        Real.logb 2 ((blockSize n (tu * w) i).choose (setSize (tu * w) i) : ℝ) -
            (1 / 40 : ℝ) * setSize (tu * w) i / 2 ≤
          minEntropy (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
              G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
            (Protocol.xi (block n (tu * w) i))) →
        mutualInfo (cond (jointLaw n (tu * w) rlaw) (fun ω =>
              G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
            (Protocol.sQi (block n (tu * w) i)) (Protocol.xi (block n (tu * w) i)) ≤
          (n : ℝ) ^ (-(1 : ℝ) / 5) →
        IsRect (Finset.powersetCard (setSize (tu * w) i) (block n (tu * w) i))
            ((1 / 40 : ℝ) * setSize (tu * w) i / 2)
            (prodDist
              (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
                  G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
                (Protocol.sQi (block n (tu * w) i)))
              (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
                  G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
                (Protocol.xi (block n (tu * w) i)))) ∧
          IsMono ((n : ℝ) ^ (-(1 : ℝ) / 10))
            (prodDist
              (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
                  G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
                (Protocol.sQi (block n (tu * w) i)))
              (law (cond (jointLaw n (tu * w) rlaw) (fun ω =>
                  G.zEvent (block n (tu * w) i) z ω ∧ Protocol.sQi (block n (tu * w) i) ω ∈ E))
                (Protocol.xi (block n (tu * w) i)))) := by sorry

end MultiphaseDisj
