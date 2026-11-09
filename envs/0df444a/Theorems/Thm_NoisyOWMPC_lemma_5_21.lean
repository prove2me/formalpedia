-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_21
-- name    : NoisyOWMPC.lemma_5_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:03:41.623385+00:00
-- url     : https://prove2.me/theorems/30b98cc4-e891-4cb6-957a-06affc57f4ed
-- title:
--   Lemma 5.21 — recoverability of the selector
-- statement:
--   There is $\gamma_0>0$ such that for every rational $\gamma_{\mathrm{sel}}\in(0,\gamma_0)$ and every expander family as in Corollary A.8 with $(c,\gamma)=(2,2/5)$ there is a constant $K$ such that for every even polynomial $N\ge\lambda$ and all large $\lambda$, in the seeded experiment of Construction 5.17, with probability at least $1-KN^{-0.013}$ over $(\mathcal T,\xi,V)$, simultaneously for every $U\subseteq V$ with $|V\setminus U|\le W$,
--   $$b_{\mathcal S}(U)\ne b_{\mathcal S}(V)\implies\xi\in\mathrm{Rec}_{\mathrm{sel}}(\mathcal T,V,U),\qquad\mathcal S=\mathrm{Recons}_{\mathrm{sel}}(\mathcal T,\xi).$$
--   The same bound holds for each fixed $\xi$, with probability over $(\mathcal T,V)$.
--
--   The proof of this lemma in Appendix B.3 is AI-assisted (p.42).
--
--   Differences from the source:
--   - reading: γ_sel a sufficiently small constant → every rational γ_sel ∈ (0, γ₀); reason: 'sufficiently small' means below a threshold; rational so that τ_sel is computable
--   - reading: 1 − O(N^{−0.013}) → 1 − K N^{−0.013} with K independent of N, for all sufficiently large λ; reason: standard reading of O
--   - generalization: the expander of Corollary A.8 with the paper's parameters (GUV graph, labels F_{M+1}^r) → any expander family satisfying the conclusion of Corollary A.8 for the stated (c, γ) (IsA8Family); reason: the statement then holds for the paper's GUV-based graph, which is one such family (Corollary A.8)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.21, p.29 (proof §B.3, p.54)

import Mathlib
import Definitions.Def_NoisyOWMPC_selectorTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family

namespace NoisyOWMPC

open Classical in
/-- The event of Lemma 5.21 for a table `T`, a seed `ξ` and an honest set `V`: simultaneously for
every `U ⊆ V` with `|V ∖ U| ≤ W`, `b_S(U) ≠ b_S(V) ⟹ ξ ∈ Rec_sel(T, V, U)`, with
`S = Recons_sel(T, ξ)` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…),
Lemma 5.21, p.29). -/
def selGood (N : ℕ → ℕ) (Gr : (M ℓ G : ℕ) → LayeredGraph M) (γsel : ℚ) (lam : ℕ)
    (T : (selectorTest N Gr γsel).St lam) (ξ : Fin ((selectorTest N Gr γsel).κ lam) → Bool)
    (V : Finset (Fin (N lam))) : Prop :=
  ∀ U ⊆ V, (V \ U).card ≤ wSel (N lam) →
    (selectorTest N Gr γsel).coin lam ((selectorTest N Gr γsel).recons lam T ξ) U ≠
      (selectorTest N Gr γsel).coin lam ((selectorTest N Gr γsel).recons lam T ξ) V →
    ξ ∈ (selectorTest N Gr γsel).recov lam T V U

/-- **Lemma 5.21 (Recoverability of the selector)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Lemma 5.21, p.29): "In the seeded experiment of Construction 5.17,
with probability at least `1 − O(N^{−0.013})` over `(T, ξ, V)`, simultaneously for every `U ⊆ V` with
`|V ∖ U| ≤ W`, `b_S(U) ≠ b_S(V) ⟹ ξ ∈ Rec_sel(T, V, U)`. The same bound holds for each fixed `ξ`,
with probability over `(T, V)`."

Construction 5.17 is `selectorTest`, with the hit-threshold constant `γ_sel` ("a sufficiently small
constant `γ_sel > 0`", p.28: every rational `γ_sel ∈ (0, γ₀)`) and the selector expander of a family
as in Corollary A.8 with `(c, γ) = (2, 2/5)` (p.28), for every even `N ≥ λ` polynomial in `λ`. The
table `T` is uniform, the seed `ξ` uniform and `V` the fair set, independently.

**Formalization Note** `O(N^{−0.013})` is `K N^{−0.013}` for a constant `K` independent of `N`, for
all large `λ`. Both sentences of the lemma are conjuncts. -/
theorem lemma_5_21 :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γsel : ℚ, 0 < γsel → (γsel : ℝ) < γ₀ →
      ∀ Gr : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family Gr 2 (2 / 5) →
        ∃ K : ℝ, ∀ N : ℕ → ℕ, AdmissibleN N → ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
          1 - K * (N lam : ℝ) ^ (-(13 / 1000 : ℝ)) ≤
            wprob (fun z : ((selectorTest N Gr γsel).St lam ×
                (Fin ((selectorTest N Gr γsel).κ lam) → Bool)) × Finset (Fin (N lam)) =>
                (selectorTest N Gr γsel).sampW lam z.1.1 *
                  (1 / 2 : ℝ) ^ ((selectorTest N Gr γsel).κ lam) * fairW (N lam) z.2)
              (fun z => selGood N Gr γsel lam z.1.1 z.1.2 z.2) ∧
          ∀ ξ : Fin ((selectorTest N Gr γsel).κ lam) → Bool,
            1 - K * (N lam : ℝ) ^ (-(13 / 1000 : ℝ)) ≤
              wprob (fun z : (selectorTest N Gr γsel).St lam × Finset (Fin (N lam)) =>
                  (selectorTest N Gr γsel).sampW lam z.1 * fairW (N lam) z.2)
                (fun z => selGood N Gr γsel lam z.1 ξ z.2) := by sorry

end NoisyOWMPC
