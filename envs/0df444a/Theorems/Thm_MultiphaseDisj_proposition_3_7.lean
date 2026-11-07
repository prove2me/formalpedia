-- Prove2me | Theorems.Thm_MultiphaseDisj_proposition_3_7
-- name    : MultiphaseDisj.proposition_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:32.74094+00:00
-- url     : https://prove2.me/theorems/c4fcfcfb-6f0e-461f-ab3b-170db9ac5a64
-- title:
--   Proposition 3.7 — the query side
-- statement:
--   Assume the standing hypotheses of §3, fix $i\in I$, and let $G$ be any protocol for epoch $i$ with the properties of Theorem 3.3(a)–(c),(e), with any finite law of $R_{\mathrm{Bob}}$ independent of $(\vec S,X)$ and $Q$. If $\rho_1\ge n^{-1/6}$ (so in particular $\rho_1>0$), then
--   $$
--   \Pr_{z\sim Z_{\mathrm{alice}}\mid B_Q=1}\Big[\exists E\subseteq\tbinom{B_i}{s_i}:\ \Pr\big[S_Q^{(i)}\in E\ \big|\ Z=(z,1)\big]\ge\tfrac34\ \text{ and }\ H_\infty\big(S_Q^{(i)}\ \big|\ Z=(z,1),\,S_Q^{(i)}\in E\big)\ge\log\tbinom{n_i}{s_i}-32n^{1/5}\Big]\ge\frac34 .
--   $$
--
--   After conditioning on a typical certified "disjoint" answer, the query-side block input keeps nearly full min-entropy on an event of constant probability: Alice's transcripts carry only $O(t_qw)$ bits about a random $S_Q$.
--
--   Differences from the source:
--   - reading: standing assumptions of §3 (w = Θ(log n), tu w ≤ n^{1/95}, tq ≤ log² n, tu, tq ≥ 1, n sufficiently large) → hypotheses: ∀ 0 < c₁ ≤ c₂, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, 1 ≤ tu, 1 ≤ tq, tu w ≤ n^{1/95}, tq ≤ (log₂ n)²; reason: §3.1 Setup, p.16, and §2.1 'state asymptotic bounds for sufficiently large instances'
--   - generalization: the protocol Gᵢ of Theorem 3.3 (with R_Bob the Bernoulli(p) bits) → every protocol with the properties of Theorem 3.3(a)–(c), the argument structure (e), and any finite law of R_Bob independent of (S⃗, X) and Q; reason: the proof (p.19: 'By Theorem 3.3(e), Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)') uses only these properties; Theorem 3.3 shows Gᵢ is such a protocol
--   - encoding: Pr_{z∼Zalice|BQ=1}[·] and E_{z∼Zalice|BQ=1}[·] → probability (expectation) over the sample space conditioned on B_Q = 1 of the quantity evaluated at z = Z_alice(ω); reason: same law of z; only attained values z, with Pr[Z = (z,1)] > 0, carry weight
--   - encoding: H, I, H∞ and log with base 2 (§2.2) → entropy, mutual information and min-entropy in bits on finite sample spaces with real point masses; reason: same quantities
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Proposition 3.7, p.20 (proof pp.20–21)

import Mathlib
import Definitions.Def_MultiphaseDisj_Protocol
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Proposition 3.7 (The query side)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Proposition 3.7, p.20). If `ρ₁ ≥ n^{−1/6}`, then
with probability at least `3/4` over `z ∼ Z_alice | B_Q = 1` there is a family
`E ⊆ (Bᵢ choose sᵢ)` with `Pr[S_Q^{(i)} ∈ E | Z = (z, 1)] ≥ 3/4` and
`H∞(S_Q^{(i)} | Z = (z, 1), S_Q^{(i)} ∈ E) ≥ log (nᵢ choose sᵢ) − 32 n^{1/5}`.

**Formalization Note** Stated for every protocol with the properties of Theorem 3.3(a)–(c),(e)
(`Protocol.IsSimProtocol` and the argument structure of `Protocol`), for any finite law of Bob's
randomness `R_Bob` independent of `(S⃗, X)` and `Q`: the proof (§3.3, p.19: "By Theorem 3.3(e),
Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)") uses only these properties.
The standing assumptions of §3 (p.16) are hypotheses: `c₁ log n ≤ w ≤ c₂ log n` for arbitrary
`0 < c₁ ≤ c₂`, `n ≥ n₀(c₁, c₂)`, `tu, tq ≥ 1`, `tu w ≤ n^{1/95}`, `tq ≤ log₂² n`, `i ∈ I`, and
`ρ₁ > 0` (p.19: "Fix i ∈ I with ρ1 > 0"), which here follows from `ρ₁ ≥ n^{−1/6}`. `Pr_{z∼Z_alice|B_Q=1}` and `E_{z∼Z_alice|B_Q=1}` are
taken over the sample space conditioned on `B_Q = 1`, so every value `z` that occurs has
`Pr[Z = (z, 1)] > 0`. Logarithms, entropies and informations are in bits; `ε = 1/40`. -/
theorem proposition_3_7 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ (tu : ℕ) (tq : ℝ), 1 ≤ tu → 1 ≤ tq →
      ((tu * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 95) → tq ≤ (Real.logb 2 n) ^ 2 →
      ∀ i ∈ epochSet n (tu * w),
      ∀ (R : Type) [Fintype R] (rlaw : R → ℝ), IsDist rlaw →
      ∀ (UT PT AT : Type) (G : Protocol n R UT PT AT), G.IsSimProtocol rlaw w tu tq i →
      (n : ℝ) ^ (-(1 : ℝ) / 6) ≤ G.rho1 (tu * w) rlaw (block n (tu * w) i) →
      (3 : ℝ) / 4 ≤ pr (cond (jointLaw n (tu * w) rlaw) (G.bq (block n (tu * w) i)))
        (fun ω => ∃ E : Finset (Finset (Fin n)),
          E ⊆ Finset.powersetCard (setSize (tu * w) i) (block n (tu * w) i) ∧
          (3 : ℝ) / 4 ≤ pr (cond (jointLaw n (tu * w) rlaw)
              (G.zEvent (block n (tu * w) i) (G.zalice (block n (tu * w) i) ω)))
            (fun ω' => Protocol.sQi (block n (tu * w) i) ω' ∈ E) ∧
          Real.logb 2 ((blockSize n (tu * w) i).choose (setSize (tu * w) i) : ℝ) -
              32 * (n : ℝ) ^ ((1 : ℝ) / 5) ≤
            minEntropy (law (cond (jointLaw n (tu * w) rlaw) (fun ω' =>
                G.zEvent (block n (tu * w) i) (G.zalice (block n (tu * w) i) ω) ω' ∧
                  Protocol.sQi (block n (tu * w) i) ω' ∈ E))
              (Protocol.sQi (block n (tu * w) i)))) := by sorry

end MultiphaseDisj
