-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_16
-- name    : NoisyOWMPC.lemma_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:07:34.064426+00:00
-- url     : https://prove2.me/theorems/9a844e30-6623-4aed-83e6-f82172d9d470
-- title:
--   Lemma 5.16 — recoverable selectors from subset majorities (corrected: N at least a constant N₀)
-- statement:
--   There is $\gamma_0>0$ such that for every rational $\gamma_{\mathrm{sel}}\in(0,\gamma_0)$ and every expander family as in Corollary A.8 with $(c,\gamma)=(2,2/5)$:
--   1. there are constants $K,K_1,K_2>0$ and $N_0$ such that for every even polynomial $N\ge\lambda$ with $N(\lambda)\ge N_0$, Construction 5.17 is a recoverable selector on $[N]$ with
--   $$\alpha_{\mathrm{sel}}=b_N:=2e^{-2r_N^2/N},\qquad\delta_{\mathrm{sel}}\le KN^{-0.013},$$
--   and seed length $K_1N^{0.0585}\log_2N\le\kappa_{\mathrm{sel}}\le K_2N^{0.0585}\log_2N$;
--   2. $\alpha_{\mathrm{sel}}=b_N$ is negligible;
--   3. for every $c>0$ and every polynomial $p$, a polynomial $N$ makes $\delta_{\mathrm{sel}}\le\lambda^{-c}$ and the seed length at least $p(\lambda)$.
--
--   Differences from the source:
--   - reading: γ_sel a sufficiently small constant → every rational γ_sel ∈ (0, γ₀); reason: 'sufficiently small' means below a threshold; rational so that τ_sel is computable
--   - reading: κ_sel = Θ(N^{0.0585} log N), δ_sel = O(N^{−0.013}), δ_sel ≤ λ^{−c} → explicit constants independent of N; bounds for all sufficiently large λ; reason: standard reading of Θ and O; Corollary A.8 supplies the expander only for large m
--   - correction: for every even polynomial N ≥ λ → for every even polynomial N ≥ λ with N(λ) ≥ N₀ for a constant N₀ (first part); reason: false as printed for small N: N(λ) = 2λ + 2 at λ = 0 gives N = 2, q₀ = 1, m = 0, so b_S ≡ 0 while Guard_sel always accepts and balance (5.6) fails; the paper itself needs 'for large N, t_sel ≤ N̄' (p.28)
--   - generalization: the expander of Corollary A.8 with the paper's parameters (GUV graph, labels F_{M+1}^r) → any expander family satisfying the conclusion of Corollary A.8 for the stated (c, γ) (IsA8Family); reason: the statement then holds for the paper's GUV-based graph, which is one such family (Corollary A.8)
--   - encoding: samplers implemented within statistical error 2^{−λ} → exact reference distributions; efficiency clauses ask for a polynomial-time sampler within 2^{−λ}; reason: the paper's own convention: 'The distributions above are exact reference distributions' (p.24)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.16, p.28

import Mathlib
import Definitions.Def_NoisyOWMPC_selectorTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family

namespace NoisyOWMPC

/-- **Lemma 5.16 (Recoverable selectors from subset majorities)** (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), Lemma 5.16, p.28): "For every even `N = N(λ) ≥ λ`
polynomial in `λ`, Construction 5.17 is a recoverable selector on `[N]` with seed length
`κ_sel = Θ(N^{0.0585} log N)` and errors `α_sel = b_N := 2e^{−2r_N²/N}`, `δ_sel = O(N^{−0.013})`. In
particular, `α_sel` is negligible, and for every `c > 0`, a polynomial `N` makes `δ_sel ≤ λ^{−c}` and
the seed length at least any prescribed polynomial."

Construction 5.17 is `selectorTest`, with the hit-threshold constant `γ_sel` ("a sufficiently small
constant", p.28: every rational `γ_sel ∈ (0, γ₀)`) and the selector expander of a family as in
Corollary A.8 with `(c, γ) = (2, 2/5)`. The conclusion has three parts:
1. for every admissible `N` with `N(λ) ≥ N₀` for all `λ`, the selector is recoverable (Definition 5.4) with `α_sel = b_N` and some
   `δ_sel ≤ K N^{−0.013}`, and `K₁ N^{0.0585} log₂ N ≤ κ_sel ≤ K₂ N^{0.0585} log₂ N`;
2. `b_N` is negligible for every admissible `N`;
3. for every `c > 0` and every polynomial `p`, some admissible `N` gives a recoverable selector with
   `δ_sel ≤ λ^{−c}` and `κ_sel ≥ p(λ)`.

**Formalization Note** The constants `K, K₁, K₂` do not depend on `N`; `O`, `Θ` and the bounds of the
third part hold for all large `λ`. Correction: the first part asks `N(λ) ≥ N₀` for a constant `N₀`
(the paper: "for large `N`, `t_sel ≤ N̄`", p.28). As printed it fails for small `N`: for `N(λ) = 2λ + 2`
at `λ = 0`, `N = 2` gives `q₀ = 1`, `m = 0`, so `b_S ≡ 0` while the guard always accepts, and balance
(5.6) fails. -/
theorem lemma_5_16 :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γsel : ℚ, 0 < γsel → (γsel : ℝ) < γ₀ →
      ∀ Gr : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family Gr 2 (2 / 5) →
        (∃ (K K₁ K₂ : ℝ) (N₀ : ℕ), 0 < K₁ ∧ 0 < K₂ ∧ ∀ N : ℕ → ℕ, AdmissibleN N →
          (∀ lam, N₀ ≤ N lam) →
          ∃ δsel : ℕ → ℝ,
            (selectorTest N Gr γsel).IsRecSelector (fun lam => bN (N lam)) δsel ∧
            ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, δsel lam ≤ K * (N lam : ℝ) ^ (-(13 / 1000 : ℝ)) ∧
              K₁ * (N lam : ℝ) ^ (585 / 10000 : ℝ) * Real.logb 2 (N lam) ≤
                ((selectorTest N Gr γsel).κ lam : ℝ) ∧
              ((selectorTest N Gr γsel).κ lam : ℝ) ≤
                K₂ * (N lam : ℝ) ^ (585 / 10000 : ℝ) * Real.logb 2 (N lam)) ∧
        (∀ N : ℕ → ℕ, AdmissibleN N → Negligible fun lam => bN (N lam)) ∧
        ∀ c : ℝ, 0 < c → ∀ p : ℕ → ℕ, PolyBounded p → ∃ N : ℕ → ℕ, AdmissibleN N ∧
          ∃ δsel : ℕ → ℝ,
            (selectorTest N Gr γsel).IsRecSelector (fun lam => bN (N lam)) δsel ∧
            ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, δsel lam ≤ (lam : ℝ) ^ (-c) ∧
              p lam ≤ (selectorTest N Gr γsel).κ lam := by sorry

end NoisyOWMPC
