-- Prove2me | Theorems.Thm_MultiphaseDisj_proposition_3_8
-- name    : MultiphaseDisj.proposition_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:41.643202+00:00
-- url     : https://prove2.me/theorems/2975fe60-8cdf-4305-b35f-07542ea86848
-- title:
--   Proposition 3.8 — the update side
-- statement:
--   Assume the standing hypotheses of §3, fix $i\in I$, and let $G$ be any protocol for epoch $i$ with the properties of Theorem 3.3(a)–(c),(e), with any finite law of $R_{\mathrm{Bob}}$ independent of $(\vec S,X)$ and $Q$, and with $\rho_1>0$. Then, with $\varepsilon=1/40$,
--   $$
--   \Pr_{z\sim Z_{\mathrm{alice}}\mid B_Q=1}\Big[H_\infty\big(X^{(i)}\ \big|\ Z=(z,1)\big)\ge\log\tbinom{n_i}{s_i}-\frac{\varepsilon s_i}4-\log\frac1{\rho_1}-2\Big]\ge\frac34 .
--   $$
--
--   The only information about $X^{(i)}$ in $Z_{\mathrm{alice}}$ is Bob's short message $\Psi$, and conditioning on $B_Q=1$ costs $\log(1/\rho_1)$ more bits.
--
--   Differences from the source:
--   - reading: standing assumptions of §3 (w = Θ(log n), tu w ≤ n^{1/95}, tq ≤ log² n, tu, tq ≥ 1, n sufficiently large) → hypotheses: ∀ 0 < c₁ ≤ c₂, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, 1 ≤ tu, 1 ≤ tq, tu w ≤ n^{1/95}, tq ≤ (log₂ n)²; reason: §3.1 Setup, p.16, and §2.1 'state asymptotic bounds for sufficiently large instances'
--   - generalization: the protocol Gᵢ of Theorem 3.3 (with R_Bob the Bernoulli(p) bits) → every protocol with the properties of Theorem 3.3(a)–(c), the argument structure (e), and any finite law of R_Bob independent of (S⃗, X) and Q; reason: the proof (p.19: 'By Theorem 3.3(e), Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)') uses only these properties; Theorem 3.3 shows Gᵢ is such a protocol
--   - reading: 'Fix i ∈ I with ρ1 > 0' (p.19) → hypothesis 0 < ρ₁; reason: standing assumption of §3.3
--   - encoding: Pr_{z∼Zalice|BQ=1}[·] and E_{z∼Zalice|BQ=1}[·] → probability (expectation) over the sample space conditioned on B_Q = 1 of the quantity evaluated at z = Z_alice(ω); reason: same law of z; only attained values z, with Pr[Z = (z,1)] > 0, carry weight
--   - encoding: H, I, H∞ and log with base 2 (§2.2) → entropy, mutual information and min-entropy in bits on finite sample spaces with real point masses; reason: same quantities
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Proposition 3.8, p.21

import Mathlib
import Definitions.Def_MultiphaseDisj_Protocol
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Proposition 3.8 (The update side)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Proposition 3.8, p.21). With probability at
least `3/4` over `z ∼ Z_alice | B_Q = 1`,
`H∞(X^{(i)} | Z = (z, 1)) ≥ log (nᵢ choose sᵢ) − ε sᵢ/4 − log(1/ρ₁) − 2`.

**Formalization Note** Stated for every protocol with the properties of Theorem 3.3(a)–(c),(e)
(`Protocol.IsSimProtocol` and the argument structure of `Protocol`), for any finite law of Bob's
randomness `R_Bob` independent of `(S⃗, X)` and `Q`: the proof (§3.3, p.19: "By Theorem 3.3(e),
Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)") uses only these properties.
The standing assumptions of §3 (p.16) are hypotheses: `c₁ log n ≤ w ≤ c₂ log n` for arbitrary
`0 < c₁ ≤ c₂`, `n ≥ n₀(c₁, c₂)`, `tu, tq ≥ 1`, `tu w ≤ n^{1/95}`, `tq ≤ log₂² n`, `i ∈ I`, and
`ρ₁ > 0` (p.19: "Fix i ∈ I with ρ1 > 0"). `Pr_{z∼Z_alice|B_Q=1}` and `E_{z∼Z_alice|B_Q=1}` are
taken over the sample space conditioned on `B_Q = 1`, so every value `z` that occurs has
`Pr[Z = (z, 1)] > 0`. Logarithms, entropies and informations are in bits; `ε = 1/40`. -/
theorem proposition_3_8 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ (tu : ℕ) (tq : ℝ), 1 ≤ tu → 1 ≤ tq →
      ((tu * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 95) → tq ≤ (Real.logb 2 n) ^ 2 →
      ∀ i ∈ epochSet n (tu * w),
      ∀ (R : Type) [Fintype R] (rlaw : R → ℝ), IsDist rlaw →
      ∀ (UT PT AT : Type) (G : Protocol n R UT PT AT), G.IsSimProtocol rlaw w tu tq i →
      0 < G.rho1 (tu * w) rlaw (block n (tu * w) i) →
      (3 : ℝ) / 4 ≤ pr (cond (jointLaw n (tu * w) rlaw) (G.bq (block n (tu * w) i)))
        (fun ω =>
          Real.logb 2 ((blockSize n (tu * w) i).choose (setSize (tu * w) i) : ℝ) -
              (1 / 40 : ℝ) * setSize (tu * w) i / 4 -
              Real.logb 2 (1 / G.rho1 (tu * w) rlaw (block n (tu * w) i)) - 2 ≤
            minEntropy (law (cond (jointLaw n (tu * w) rlaw)
                (G.zEvent (block n (tu * w) i) (G.zalice (block n (tu * w) i) ω)))
              (Protocol.xi (block n (tu * w) i)))) := by sorry

end MultiphaseDisj
