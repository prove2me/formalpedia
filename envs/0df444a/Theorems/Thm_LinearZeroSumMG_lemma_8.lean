-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_8
-- name    : LinearZeroSumMG.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:54:03.210111+00:00
-- url     : https://prove2.me/theorems/063c6d21-ec4a-4194-aa1b-703d880c7765
-- title:
--   Lemma 8, p.28 — $\|\overline w^k_h\|,\|\underline w^k_h\|\le2H\sqrt{dk}$ (and the generic ridge bound covering Algorithm 3)
-- statement:
--   **Lemma 8 (Algorithm coefficients are bounded).** The statement has two parts.
--
--   1. Let $d,H,k\in\mathbb N$, let $\psi_1,\dots,\psi_{k-1}\in\mathbb R^d$ with $\|\psi_\tau\|\le1$, and let $y_1,\dots,y_{k-1}\in\mathbb R$ with $|y_\tau|\le2H$. Then
--   $$
--   \Big\|\Big(I+\sum_{\tau=1}^{k-1}\psi_\tau\psi_\tau^\top\Big)^{-1}\sum_{\tau=1}^{k-1}y_\tau\psi_\tau\Big\|\le2H\sqrt{dk}.
--   $$
--   2. For every game with rewards in $[-1,1]$, every feature map with $\|\phi\|\le1$, every bonus $\beta$, every CCE rule whose outputs are probability distributions, every rounding rule and every data sequence, the coefficients of Algorithm 1 satisfy
--   $$
--   \|\overline w^k_h\|\le2H\sqrt{dk},\qquad\|\underline w^k_h\|\le2H\sqrt{dk}\qquad\text{for all }k\text{ and }h\in[H].
--   $$
--
--   Part 1 also bounds the coefficients $w^k_h$ of the paper's online Algorithm 3, whose regression targets $r_h+V^k_{h+1}$ lie in $[-2H,2H]$. The bound is what places the algorithm's estimates inside the class $\mathcal Q$ of (5), so that they can be rounded into its $\varepsilon$-net.
--
--   Differences from the source:
--   - generalization: the coefficients {w^k_h} of Algorithm 3 → a generic ridge-regression bound for any ψ_τ with ‖ψ_τ‖ ≤ 1 and targets |y_τ| ≤ 2H; reason: Algorithm 3's regression targets r_h + V^k_{h+1} lie in [−1 − H, 1 + H] ⊆ [−2H, 2H], so its clause is a special case; Algorithm 3 is not defined in this mission
--   - generalization: the coefficients of Algorithm 1 for k ∈ [K], under Assumption 1 → every game with rewards in [−1, 1], every feature map with ‖φ‖ ≤ 1, every β, every CCE rule returning distributions, every rounding rule, every data sequence and every k ∈ ℕ; reason: the proof uses only |r_h| ≤ 1, ‖φ‖ ≤ 1 and |V̄^k_{h+1}|, |V̲^k_{h+1}| ≤ H; the setting of Algorithm 1 is a special case
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 8, p.28

import Mathlib
import Definitions.Def_LinearZeroSumMG_omni

open Matrix

namespace LinearZeroSumMG

/-- **Lemma 8 (Algorithm Coefficients Are Bounded).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 8, p.28: "The coefficients
`{w̄^k_h, w̲^k_h}` in Algorithm 1 and the coefficients `{w^k_h}` in Algorithm 3 satisfy
`‖w̄^k_h‖ ≤ 2H√(dk)`, `‖w̲^k_h‖ ≤ 2H√(dk)`, and `‖w^k_h‖ ≤ 2H√(dk)`, `∀(k, h) ∈ [K] × [H]`."

Two parts.
1. (Generic ridge bound, which covers Algorithm 3.) For all `d, H, k`, vectors `ψ_τ ∈ ℝ^d` and reals
   `y_τ` with `‖ψ_τ‖ ≤ 1` and `|y_τ| ≤ 2H` for `τ ∈ [1, k − 1]`,
   `‖(I + ∑_{τ=1}^{k−1} ψ_τψ_τᵀ)⁻¹ ∑_{τ=1}^{k−1} y_τψ_τ‖ ≤ 2H√(dk)`.
2. (Algorithm 1.) For every game with rewards in `[−1, 1]`, every feature map with `‖φ‖ ≤ 1`, every
   `β`, every CCE rule returning distributions, every rounding rule and every data sequence,
   `‖w̄^k_h‖ ≤ 2H√(dk)` and `‖w̲^k_h‖ ≤ 2H√(dk)` for all `k` and `h ∈ [1, H]`.

**Formalization Note** Part 1 covers Algorithm 3's coefficients without defining Algorithm 3: its
targets `r_h + V^k_{h+1}` lie in `[−1 − H, 1 + H] ⊆ [−2H, 2H]`. Part 2 holds for every data sequence,
not only on the event `𝔈`, and does not use the linear structure of the game. -/
theorem lemma_8 :
    (∀ (d H k : ℕ) (ψ : ℕ → Fin d → ℝ) (y : ℕ → ℝ),
      (∀ τ ∈ Finset.Ico 1 k, ApproxVI.euclNorm (ψ τ) ≤ 1) → (∀ τ ∈ Finset.Ico 1 k, |y τ| ≤ 2 * H) →
      ApproxVI.euclNorm ((∑ τ ∈ Finset.Ico 1 k, vecMulVec (ψ τ) (ψ τ) + 1)⁻¹ *ᵥ
          ∑ τ ∈ Finset.Ico 1 k, y τ • ψ τ) ≤ 2 * H * Real.sqrt (d * k)) ∧
    (∀ {S A : Type} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}
      (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S) (as bs : ℕ → ℕ → A),
      (∀ x a b, ApproxVI.euclNorm (P.φ x a b) ≤ 1) →
      (∀ u₁ u₂ : A → A → ℝ, P.cce u₁ u₂ ∈ stdSimplex ℝ (A × A)) →
      ∀ (k : ℕ), ∀ h ∈ Finset.Icc 1 G.H,
        ApproxVI.euclNorm (omni G P xs as bs k h).wUp ≤ 2 * G.H * Real.sqrt (d * k) ∧
        ApproxVI.euclNorm (omni G P xs as bs k h).wLo ≤ 2 * G.H * Real.sqrt (d * k)) := by sorry

end LinearZeroSumMG
