-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_5
-- name    : NoisyOWMPC.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:04:35.590668+00:00
-- url     : https://prove2.me/theorems/84cc697b-b7a2-4f08-857e-9ed12e1c7c11
-- title:
--   Lemma 5.5 — access tests from non-degradation
-- statement:
--   Let $k>1$ and $C_i\not\preceq\mathbf C_{-i}$. There is $\tau_0>0$ such that for every rational $\tau_{\mathrm{acc}}\in(0,\tau_0)$, every stochastic row $e_0$, every expander family as in Corollary A.8 with $(c,\gamma)=(2,2/5)$, every family $\mathrm{apx}$ and every polynomial $M\ge\lambda^5$ with $M+1$ a power of two, Construction 5.6 is a **recoverable access test** for $i$ (Definition 5.2) with channel-input length $M^3$, negligible errors $\alpha$ and $\delta_{\mathrm{acc}}$, and seed length at least $\lambda$.
--
--   The algorithms $\mathrm{Gen}$, $\mathrm{Word}$ and $A_\Omega$ depend only on $C_i$. This is the access-test instantiation behind Theorem 5.22.
--
--   Differences from the source:
--   - reading: a constant τ_acc ∈ (0,1) chosen in Section B.1 as a function of E → every rational τ_acc ∈ (0, τ₀) for some τ₀ > 0 depending on the channel; reason: B.1 chooses any rational 0 < τ_acc < min{Δ/16, 1/16}
--   - encoding: 'use any stochastic row for an empty set' → a stochastic row e₀, quantified universally; reason: the paper allows any such row
--   - reading: seed length at least λ → seed length at least λ for all sufficiently large λ; reason: the seed length comes from Corollary A.8, which supplies the expander only for all sufficiently large M
--   - encoding: 'The algorithms Gen, Word, and A_Ω depend only on C_i' → not a separate clause: accessHalfN reads only apx λ i; reason: it holds by the definition of the construction
--   - encoding: recoverable access test → ChannelTest.IsRecAccess, which includes the efficiency of all algorithms and the polynomial channel-input length; reason: Definition 5.1 and §3 require polynomial-time algorithms
--   - generalization: the expander of Corollary A.8 with the paper's parameters (GUV graph, labels F_{M+1}^r) → any expander family satisfying the conclusion of Corollary A.8 for the stated (c, γ) (IsA8Family); reason: the statement then holds for the paper's GUV-based graph, which is one such family (Corollary A.8)
--   - generalization: fixed public rational upper approximations within 2^{−λ}, chosen deterministically → every polynomial-time computable family apx with C ≤ apx ≤ C + 2^{−λ}; reason: the paper's fixed choice is one such family; the analysis uses only these bounds (§5 Conventions, p.21)
--   - encoding: samplers implemented within statistical error 2^{−λ} → exact reference distributions; efficiency clauses ask for a polynomial-time sampler within 2^{−λ}; reason: the paper's own convention: 'The distributions above are exact reference distributions' (p.24)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.5, p.24

import Mathlib
import Definitions.Def_NoisyOWMPC_accessTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family

namespace NoisyOWMPC

/-- **Lemma 5.5 (Access tests from non-degradation)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Lemma 5.5, p.24): "Let `k > 1` and `C_i ⋠ C_{−i}`. For every
polynomial `M = M(λ) ≥ λ⁵` with `M + 1` a power of two, Construction 5.6 is a recoverable access
test for `i` with channel-input length polynomial in `λ`, seed length at least `λ`, and negligible
errors `α` and `δ_acc`. The algorithms `Gen`, `Word`, and `A_Ω` depend only on `C_i`."

Construction 5.6 is `accessTest`, with the threshold `τ_acc` of Section B.1 (any rational
`0 < τ_acc < τ₀`, `τ₀` depending on the channel), any stochastic row `e₀` for the empty sets of
(5.10), the access expander of a family as in Corollary A.8 with `(c, γ) = (2, 2/5)` (p.25), and
rational approximations `apx`.

**Formalization Note** "Recoverable access test" is `ChannelTest.IsRecAccess` (Definition 5.2, with
the efficiency of the algorithms; the channel-input length `n = M³` is polynomial there). "Seed
length at least `λ`" is stated for all large `λ`: the expander of Corollary A.8 exists for all
sufficiently large `M`. That `Gen`, `Word` and `A_Ω` depend only on `C_i` holds by definition:
`accessHalfN` reads only the approximations `apx λ i` of `C_i`. -/
theorem lemma_5_5 {k : ℕ} (hk : 1 < k) {X : Type} [Fintype X] {Y : Fin k → Type}
    [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i)) (i : Fin k)
    (hnd : ¬ Degraded (C i).P (minusP C i)) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℚ, 0 < τ → (τ : ℝ) < τ₀ →
      ∀ e0 : Y i → ℚ, (∀ b, 0 ≤ e0 b) → ∑ b, e0 b = 1 →
      ∀ Gr : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family Gr 2 (2 / 5) →
      ∀ apx : ℕ → ∀ i, X → Y i → ℚ, IsApx C apx →
      ∀ M : ℕ → ℕ, AdmissibleM M →
        ∃ α δacc : ℕ → ℝ, Negligible α ∧ Negligible δacc ∧
          (accessTest C apx M i Gr τ e0).IsRecAccess C α δacc ∧
          ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, lam ≤ (accessTest C apx M i Gr τ e0).κ lam := by sorry

end NoisyOWMPC
