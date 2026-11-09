-- Prove2me | Theorems.Thm_NoisyOWMPC_theorem_5_22
-- name    : NoisyOWMPC.theorem_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:05:27.870854+00:00
-- url     : https://prove2.me/theorems/5c7c372e-5261-4b73-a14a-675432a2d3a1
-- title:
--   Theorem 5.22 — recoverable tests from noise preservation (corrected: unbiasedness allows p′ ∈ {0,1} at small λ)
-- statement:
--   Let $\mathbf C$ be a product broadcast channel satisfying noise preservation with bits $\beta$. There is $\tau_0>0$ such that for every rational $\tau_{\mathrm{acc}}\in(0,\tau_0)$, all stochastic rows $e_0$, expander families as in Corollary A.8 with $(c,\gamma)=(2,2/5)$ (access) and $(8,2/5)$ (release), and rational approximations $\mathrm{apx}$, there is a constant $K$ such that:
--   1. for every polynomial $M\ge\lambda^5$ with $M+1$ a power of two, when $k>1$ every receiver's Construction 5.6 is a recoverable access test with negligible errors, and every receiver's Construction 5.11 is a recoverable release test with errors at most $KM^{-1/10}$; channel-input lengths are polynomial and seed lengths are at least $\lambda$;
--   2. for every $c>0$ and every polynomial $p$, one such $M$ makes all four errors at most $\lambda^{-c}$ and both seed lengths at least $p(\lambda)$.
--
--   No cryptographic assumption is used. In unbiasedness the number $p'$ is only required to lie in $[0,1]$, which agrees with Definition 5.3 whenever $\eta<\tfrac12$.
--
--   Differences from the source:
--   - reading: a constant τ_acc chosen in Section B.1 → every rational τ_acc ∈ (0, τ₀); reason: B.1 chooses any rational 0 < τ_acc < min{Δ/16, 1/16}
--   - encoding: 'use any stochastic row for an empty set' → stochastic rows e₀, quantified universally; reason: the paper allows any such row
--   - reading: release errors O(M^{−1/10}); errors at most λ^{−c}; seed lengths at least λ (or a prescribed polynomial) → bounds K M^{−1/10} (K independent of M), λ^{−c} and seed lengths, each for all sufficiently large λ; reason: standard reading of O; Corollary A.8 supplies the expander only for large M
--   - correction: Definition 5.3: p′ ∈ (0,1) with |p′ − ½| ≤ η, claimed for every λ → p′ ∈ [0,1] with |p′ − ½| ≤ η (equivalent whenever η < ½, in particular for all large λ); reason: false as printed at small λ under the paper's rounding convention: λ = 4, M = 2047, apx ∈ [C + 2^{−5}, C + 2^{−4}] rational; then some (x, z) has N_x·apx − n_{x,z} ≥ N_x/32 = 2047⁸/16 > a_t = ⌈(2d·2047⁸)^{0.55}⌉ for every query, so Check rejects every row and p′ = 0
--   - generalization: the expander of Corollary A.8 with the paper's parameters (GUV graph, labels F_{M+1}^r) → any expander family satisfying the conclusion of Corollary A.8 for the stated (c, γ) (IsA8Family); reason: the statement then holds for the paper's GUV-based graph, which is one such family (Corollary A.8)
--   - generalization: fixed public rational upper approximations within 2^{−λ}, chosen deterministically → every polynomial-time computable family apx with C ≤ apx ≤ C + 2^{−λ}; reason: the paper's fixed choice is one such family; the analysis uses only these bounds (§5 Conventions, p.21)
--   - encoding: samplers implemented within statistical error 2^{−λ} → exact reference distributions; efficiency clauses ask for a polynomial-time sampler within 2^{−λ}; reason: the paper's own convention: 'The distributions above are exact reference distributions' (p.24)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem 5.22, p.30

import Mathlib
import Definitions.Def_NoisyOWMPC_accessTest
import Definitions.Def_NoisyOWMPC_releaseTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family
import Definitions.Def_NoisyOWMPC_NoisePreserving

namespace NoisyOWMPC

/-- **Theorem 5.22 (Recoverable tests from noise preservation)** (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), Theorem 5.22, p.30): "For every fixed channel satisfying
Definition 4.5 and every polynomial `M = M(λ) ≥ λ⁵` with `M + 1` a power of two, Constructions 5.6
and 5.11 are recoverable access tests (when `k > 1`) and release tests in the sense of Definitions
5.2 and 5.3, without any cryptographic assumption. Their channel-input lengths are polynomial in
`λ`, their seed lengths are at least `λ`, the access errors are negligible, and the release errors
are `O(M^{−1/10})`. In particular, for every `c > 0`, a polynomial `M` makes all four errors at most
`λ^{−c}` and both seed lengths at least any prescribed polynomial."

For a product broadcast channel with noise-preservation bits `β`, there is a threshold `τ₀ > 0` such
that for every rational `τ_acc ∈ (0, τ₀)`, all stochastic rows `e₀` for the empty sets of (5.10),
expander families as in Corollary A.8 with `(c, γ) = (2, 2/5)` (access) and `(8, 2/5)` (release),
and rational approximations `apx`, there is a constant `K` with:
1. for every admissible `M`: when `k > 1`, each receiver's Construction 5.6 is a recoverable access
   test with negligible errors and seed length at least `λ`; each receiver's Construction 5.11 is a
   recoverable release test with errors at most `K M^{−1/10}` and seed length at least `λ`;
2. for every `c > 0` and every polynomial `p`, one admissible `M` makes every receiver's tests
   recoverable with all four errors at most `λ^{−c}` and both seed lengths at least `p(λ)`.

**Formalization Note** Seed lengths and the bounds `λ^{−c}`, `K M^{−1/10}` are stated for all large
`λ` (the expander of Corollary A.8 exists for all sufficiently large `M`); `K` does not depend on
`M`. No cryptographic object appears among the hypotheses. -/
theorem theorem_5_22 {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]
    (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool) (hβ : NoisePreserving C β) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℚ, 0 < τ → (τ : ℝ) < τ₀ →
      ∀ e0 : ∀ i, Y i → ℚ, (∀ i b, 0 ≤ e0 i b) → (∀ i, ∑ b, e0 i b = 1) →
      ∀ GrA : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family GrA 2 (2 / 5) →
      ∀ GrR : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family GrR 8 (2 / 5) →
      ∀ apx : ℕ → ∀ i, X → Y i → ℚ, IsApx C apx →
      ∃ K : ℝ,
        (∀ M : ℕ → ℕ, AdmissibleM M →
          (1 < k → ∀ i, ∃ α δacc : ℕ → ℝ, Negligible α ∧ Negligible δacc ∧
            (accessTest C apx M i GrA τ (e0 i)).IsRecAccess C α δacc ∧
            ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, lam ≤ (accessTest C apx M i GrA τ (e0 i)).κ lam) ∧
          (∀ i, ∃ η δrel : ℕ → ℝ,
            (∃ lam₀ : ℕ, ∀ lam ≥ lam₀, η lam ≤ K * (M lam : ℝ) ^ (-(1 / 10 : ℝ)) ∧
              δrel lam ≤ K * (M lam : ℝ) ^ (-(1 / 10 : ℝ))) ∧
            (releaseTest C apx β M i GrR).IsRecRelease C η δrel ∧
            ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, lam ≤ (releaseTest C apx β M i GrR).κ lam)) ∧
        ∀ c : ℝ, 0 < c → ∀ p : ℕ → ℕ, PolyBounded p → ∃ M : ℕ → ℕ, AdmissibleM M ∧
          (1 < k → ∀ i, ∃ α δacc : ℕ → ℝ,
            (accessTest C apx M i GrA τ (e0 i)).IsRecAccess C α δacc ∧
            ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, α lam ≤ (lam : ℝ) ^ (-c) ∧ δacc lam ≤ (lam : ℝ) ^ (-c) ∧
              p lam ≤ (accessTest C apx M i GrA τ (e0 i)).κ lam) ∧
          (∀ i, ∃ η δrel : ℕ → ℝ, (releaseTest C apx β M i GrR).IsRecRelease C η δrel ∧
            ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, η lam ≤ (lam : ℝ) ^ (-c) ∧ δrel lam ≤ (lam : ℝ) ^ (-c) ∧
              p lam ≤ (releaseTest C apx β M i GrR).κ lam) := by sorry

end NoisyOWMPC
