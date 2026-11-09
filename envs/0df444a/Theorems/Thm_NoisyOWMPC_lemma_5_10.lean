-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_10
-- name    : NoisyOWMPC.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:05:18.585582+00:00
-- url     : https://prove2.me/theorems/004ce0bf-8b90-4964-9dad-62ad67b0b45e
-- title:
--   Lemma 5.10 — release tests from preserved noise (corrected: unbiasedness allows p′ ∈ {0,1} at small λ)
-- statement:
--   Let receiver $i$ have a bit $\beta_i$ satisfying noise preservation; take an expander family as in Corollary A.8 with $(c,\gamma)=(8,2/5)$ and rational approximations $\mathrm{apx}$. Then:
--   1. there is $K$ such that for every polynomial $M\ge\lambda^5$ with $M+1$ a power of two, Construction 5.11 is a **recoverable release test** for $i$ (Definition 5.3) with channel-input length $2dM^9$, errors $\eta,\delta_{\mathrm{rel}}\le KM^{-1/10}$ and seed length at least $\lambda$;
--   2. for every $c>0$ some such polynomial $M$ makes both errors at most $\lambda^{-c}$.
--
--   In unbiasedness the number $p'$ is only required to lie in $[0,1]$; this agrees with Definition 5.3 whenever $\eta<\tfrac12$, in particular for all large $\lambda$.
--
--   Differences from the source:
--   - reading: errors η, δ_rel = O(M^{−1/10}) → η, δ_rel ≤ K M^{−1/10} for all large λ, K independent of M; reason: standard reading of O
--   - reading: a polynomial M makes both errors at most λ^{−c} → both errors at most λ^{−c} for all sufficiently large λ; reason: λ^{−c} is 0 at λ = 0 in Lean, and the bounds are asymptotic
--   - reading: seed length at least λ → seed length at least λ for all sufficiently large λ; reason: the seed length comes from Corollary A.8, which supplies the expander only for all sufficiently large M
--   - encoding: recoverable release test → ChannelTest.IsRecRelease, which includes the efficiency of all algorithms and the polynomial channel-input length; reason: Definition 5.1 and §3 require polynomial-time algorithms
--   - correction: Definition 5.3: p′ ∈ (0,1) with |p′ − ½| ≤ η, claimed for every λ → p′ ∈ [0,1] with |p′ − ½| ≤ η (equivalent whenever η < ½, in particular for all large λ); reason: false as printed at small λ under the paper's rounding convention: λ = 4, M = 2047, apx ∈ [C + 2^{−5}, C + 2^{−4}] rational; then some (x, z) has N_x·apx − n_{x,z} ≥ N_x/32 = 2047⁸/16 > a_t = ⌈(2d·2047⁸)^{0.55}⌉ for every query, so Check rejects every row and p′ = 0
--   - generalization: the expander of Corollary A.8 with the paper's parameters (GUV graph, labels F_{M+1}^r) → any expander family satisfying the conclusion of Corollary A.8 for the stated (c, γ) (IsA8Family); reason: the statement then holds for the paper's GUV-based graph, which is one such family (Corollary A.8)
--   - generalization: fixed public rational upper approximations within 2^{−λ}, chosen deterministically → every polynomial-time computable family apx with C ≤ apx ≤ C + 2^{−λ}; reason: the paper's fixed choice is one such family; the analysis uses only these bounds (§5 Conventions, p.21)
--   - encoding: samplers implemented within statistical error 2^{−λ} → exact reference distributions; efficiency clauses ask for a polynomial-time sampler within 2^{−λ}; reason: the paper's own convention: 'The distributions above are exact reference distributions' (p.24)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.10, p.26

import Mathlib
import Definitions.Def_NoisyOWMPC_releaseTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family
import Definitions.Def_NoisyOWMPC_NoisePreserving

namespace NoisyOWMPC

/-- **Lemma 5.10 (Release tests from preserved noise)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Lemma 5.10, p.26): "Let `i` be a receiver with a bit `β_i`
satisfying noise preservation (Definition 4.5). For every polynomial `M = M(λ) ≥ λ⁵` with `M + 1`
a power of two, Construction 5.11 is a recoverable release test for `i` with channel-input length
polynomial in `λ`, seed length at least `λ`, and errors `η, δ_rel = O(M^{−1/10})`. In particular,
for every `c > 0`, a polynomial `M` makes both errors at most `λ^{−c}`."

Construction 5.11 is `releaseTest`, with the release expander of a family as in Corollary A.8 with
`(c, γ) = (8, 2/5)` (p.26) and rational approximations `apx`. The conclusion has two parts:
1. for every admissible `M`, the test is a recoverable release test (Definition 5.3, with efficient
   algorithms and polynomial channel-input length `n_rel = 2dM⁹`) with errors `η, δ_rel` at most
   `K M^{−1/10}` for all large `λ`, and its seed length is at least `λ` for all large `λ`;
2. for every `c > 0` some admissible `M` makes it a recoverable release test with both errors at
   most `λ^{−c}` for all large `λ`.

**Formalization Note** The constant `K` of `O(M^{−1/10})` does not depend on `M`. "Seed length at
least `λ`" and the error bounds are stated for all large `λ`: the expander of Corollary A.8 exists for
all sufficiently large `M`, and `λ^{−c}` is `0` at `λ = 0` in Lean. -/
theorem lemma_5_10 {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]
    (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool) (i : Fin k)
    (hβ : NoisePreservingAt C i (β i))
    (Gr : (M ℓ G : ℕ) → LayeredGraph M) (hGr : IsA8Family Gr 8 (2 / 5))
    (apx : ℕ → ∀ i, X → Y i → ℚ) (hapx : IsApx C apx) :
    (∃ K : ℝ, ∀ M : ℕ → ℕ, AdmissibleM M → ∃ η δrel : ℕ → ℝ,
      (∃ lam₀ : ℕ, ∀ lam ≥ lam₀, η lam ≤ K * (M lam : ℝ) ^ (-(1 / 10 : ℝ)) ∧
        δrel lam ≤ K * (M lam : ℝ) ^ (-(1 / 10 : ℝ))) ∧
      (releaseTest C apx β M i Gr).IsRecRelease C η δrel ∧
      ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, lam ≤ (releaseTest C apx β M i Gr).κ lam) ∧
    ∀ c : ℝ, 0 < c → ∃ M : ℕ → ℕ, AdmissibleM M ∧ ∃ η δrel : ℕ → ℝ,
      (releaseTest C apx β M i Gr).IsRecRelease C η δrel ∧
      ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, η lam ≤ (lam : ℝ) ^ (-c) ∧ δrel lam ≤ (lam : ℝ) ^ (-c) := by sorry

end NoisyOWMPC
