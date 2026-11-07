-- Prove2me | Theorems.Thm_MultiphaseDisj_lemma_3_13
-- name    : MultiphaseDisj.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:47.561814+00:00
-- url     : https://prove2.me/theorems/73088821-0c20-4065-b882-c6bfb39bac03
-- title:
--   Lemma 3.13 — communication lower bound $\rho_1<n^{-1/6}$
-- statement:
--   Assume the standing hypotheses of §3 and fix $i\in I$. Every protocol $G$ for epoch $i$ with the properties of Theorem 3.3(a)–(c),(e), with any finite law of $R_{\mathrm{Bob}}$ independent of $(\vec S,X)$ and $Q$, certifies "disjoint" rarely:
--   $$
--   \rho_1=\Pr_{\mathcal D,R_{\mathrm{Bob}},Q}[B_Q=1]<n^{-1/6}.
--   $$
--   In particular this holds for the protocol $G_i$ of Theorem 3.3.
--
--   Together with Theorem 3.3(d) this forces $\tau_i$ to be large for every Chronogram epoch, which gives the main theorem.
--
--   Differences from the source:
--   - reading: standing assumptions of §3 (w = Θ(log n), tu w ≤ n^{1/95}, tq ≤ log² n, tu, tq ≥ 1, n sufficiently large) → hypotheses: ∀ 0 < c₁ ≤ c₂, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, 1 ≤ tu, 1 ≤ tq, tu w ≤ n^{1/95}, tq ≤ (log₂ n)²; reason: §3.1 Setup, p.16, and §2.1 'state asymptotic bounds for sufficiently large instances'
--   - generalization: the protocol Gᵢ of Theorem 3.3 (with R_Bob the Bernoulli(p) bits) → every protocol with the properties of Theorem 3.3(a)–(c), the argument structure (e), and any finite law of R_Bob independent of (S⃗, X) and Q; reason: the proof (p.19: 'By Theorem 3.3(e), Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)') uses only these properties; Theorem 3.3 shows Gᵢ is such a protocol
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Lemma 3.13, p.24

import Mathlib
import Definitions.Def_MultiphaseDisj_Protocol
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Lemma 3.13 (Communication lower bound)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Lemma 3.13, p.24). For every `i ∈ I`, the
protocol `Gᵢ` of Theorem 3.3 has `ρ₁ < n^{−1/6}`.

**Formalization Note** Stated for every protocol with the properties of Theorem 3.3(a)–(c),(e)
(`Protocol.IsSimProtocol` and the argument structure of `Protocol`), for any finite law of Bob's
randomness `R_Bob` independent of `(S⃗, X)` and `Q`: the proof (§3.3, p.19: "By Theorem 3.3(e),
Aall is a function of (⃗S, Φ), and BQ is a function of (Zalice, U)") uses only these properties.
The standing assumptions of §3 (p.16) are hypotheses: `c₁ log n ≤ w ≤ c₂ log n` for arbitrary
`0 < c₁ ≤ c₂`, `n ≥ n₀(c₁, c₂)`, `tu, tq ≥ 1`, `tu w ≤ n^{1/95}`, `tq ≤ log₂² n`, `i ∈ I`, and
`ρ₁ > 0` (p.19: "Fix i ∈ I with ρ1 > 0"). `Pr_{z∼Z_alice|B_Q=1}` and `E_{z∼Z_alice|B_Q=1}` are
taken over the sample space conditioned on `B_Q = 1`, so every value `z` that occurs has
`Pr[Z = (z, 1)] > 0`. Logarithms, entropies and informations are in bits; `ε = 1/40`. The hypothesis `ρ₁ > 0` is not needed here and is not assumed. -/
theorem lemma_3_13 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ (tu : ℕ) (tq : ℝ), 1 ≤ tu → 1 ≤ tq →
      ((tu * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 95) → tq ≤ (Real.logb 2 n) ^ 2 →
      ∀ i ∈ epochSet n (tu * w),
      ∀ (R : Type) [Fintype R] (rlaw : R → ℝ), IsDist rlaw →
      ∀ (UT PT AT : Type) (G : Protocol n R UT PT AT), G.IsSimProtocol rlaw w tu tq i →
      G.rho1 (tu * w) rlaw (block n (tu * w) i) < (n : ℝ) ^ (-(1 : ℝ) / 6) := by sorry

end MultiphaseDisj
