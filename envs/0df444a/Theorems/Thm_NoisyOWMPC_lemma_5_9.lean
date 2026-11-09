-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_9
-- name    : NoisyOWMPC.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:04:17.939026+00:00
-- url     : https://prove2.me/theorems/b1734ccd-6fc3-42d2-b900-4ce487f80eb1
-- title:
--   Lemma 5.9 — recoverability of the access test
-- statement:
--   Let $k>1$ and let receiver $i$ satisfy $C_i\not\preceq\mathbf C_{-i}$. There is $\tau_0>0$ (depending on the channel) such that for every rational threshold $\tau_{\mathrm{acc}}\in(0,\tau_0)$, every stochastic row $e_0$ for the empty sets of (5.10), every expander family as in Corollary A.8 with $(c,\gamma)=(2,2/5)$ and every family $\mathrm{apx}$ of rational approximations, there is $c>0$ such that for every polynomial $M\ge\lambda^5$ with $M+1$ a power of two and all large $\lambda$, in the seeded experiment of Construction 5.6
--   $$\Pr_{\mathrm{st},\sigma}\bigl[\exists y:\ A_{\mathrm{Recons}(\mathrm{st},\sigma)}(y)=1\text{ and }\sigma\notin\mathrm{Rec}(\mathrm{st},y)\bigr]\le e^{-cM^3}.$$
--
--   In words: except with probability $e^{-\Omega(M^3)}$ over $\mathrm{st}$ and $\sigma$, every query accepted by the reconstructed access test reveals the seed through the recovery list. This is the recoverability half of Lemma 5.5.
--
--   Differences from the source:
--   - reading: e^{−Ω(M³)} → exp(−c M³) for a constant c > 0 independent of M and all sufficiently large λ; reason: standard reading of Ω; B.2 holds 'for all sufficiently large M'
--   - reading: a constant τ_acc ∈ (0,1) chosen in Section B.1 as a function of E → every rational τ_acc ∈ (0, τ₀) for some τ₀ > 0 depending on the channel; reason: B.1 chooses any rational 0 < τ_acc < min{Δ/16, 1/16}
--   - encoding: 'use any stochastic row for an empty set' → a stochastic row e₀, quantified universally; reason: the paper allows any such row
--   - generalization: the expander of Corollary A.8 with the paper's parameters (GUV graph, labels F_{M+1}^r) → any expander family satisfying the conclusion of Corollary A.8 for the stated (c, γ) (IsA8Family); reason: the statement then holds for the paper's GUV-based graph, which is one such family (Corollary A.8)
--   - generalization: fixed public rational upper approximations within 2^{−λ}, chosen deterministically → every polynomial-time computable family apx with C ≤ apx ≤ C + 2^{−λ}; reason: the paper's fixed choice is one such family; the analysis uses only these bounds (§5 Conventions, p.21)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.9, p.25 (setting of Lemma 5.5, p.24; τ_acc from §B.1, p.49)

import Mathlib
import Definitions.Def_NoisyOWMPC_accessTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family

namespace NoisyOWMPC

/-- **Lemma 5.9 (Recoverability of the access test)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Lemma 5.9, p.25, in the setting of Lemma 5.5, p.24): "Except with
probability `e^{−Ω(M³)}` over `st` and `σ`, every query `y` with `A_{Recons(st,σ)}(y) = 1` satisfies
`σ ∈ Rec(st, y)`."

Setting: `k > 1` receivers, `C_i ⋠ C_{−i}`, Construction 5.6 with the recovery threshold `τ_acc`
"chosen in Section B.1 as a function of `E`" (B.1, p.49: "Choose the rational constant `τ_acc` of
(5.10) with `0 < τ_acc < min{Δ/16, 1/16}`"), any stochastic row `e₀` for the empty sets of (5.10),
the access expander of a family as in Corollary A.8 with `(c, γ) = (2, 2/5)` (p.25), rational
approximations `apx`, and every polynomial `M ≥ λ⁵` with `M + 1` a power of two.

**Formalization Note** `e^{−Ω(M³)}` is `exp(−c M³)` for a constant `c > 0` (depending on the channel,
`τ_acc`, the expander family and `apx`, not on `M`) and all large `λ`. The threshold bound `τ₀` depends
only on the channel. -/
theorem lemma_5_9 {k : ℕ} (hk : 1 < k) {X : Type} [Fintype X] {Y : Fin k → Type}
    [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i)) (i : Fin k)
    (hnd : ¬ Degraded (C i).P (minusP C i)) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℚ, 0 < τ → (τ : ℝ) < τ₀ →
      ∀ e0 : Y i → ℚ, (∀ b, 0 ≤ e0 b) → ∑ b, e0 b = 1 →
      ∀ Gr : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family Gr 2 (2 / 5) →
      ∀ apx : ℕ → ∀ i, X → Y i → ℚ, IsApx C apx →
        ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ, AdmissibleM M → ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
          wprob ((accessTest C apx M i Gr τ e0).seedW lam) (fun z => ∃ y,
              (accessTest C apx M i Gr τ e0).test lam
                ((accessTest C apx M i Gr τ e0).recons lam z.1 z.2) y = true ∧
              z.2 ∉ (accessTest C apx M i Gr τ e0).recov lam z.1 y) ≤
            Real.exp (-c * (M lam : ℝ) ^ 3) := by sorry

end NoisyOWMPC
