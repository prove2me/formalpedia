-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_5_2
-- name    : OptHedgeGames.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:39:27.888216+00:00
-- url     : https://prove2.me/theorems/cef2b7dd-78db-42fe-87c0-381fe8eda29d
-- title:
--   Lemma 5.2 — the interior Bernstein inequality in $L^2$ form
-- statement:
--   Let $K$ be a real inner product space, let $N(s)=\sum_{k=1}^nw_ke^{\lambda_ks}$ with $w_k\in K$ and $\lambda_k\in\mathbb R$, and let $I=[\alpha+W,\alpha+2W]$ be the middle third of $J=[\alpha,\alpha+3W]$, for $\alpha\in\mathbb R$ and $W>0$. Then
--   $$
--   \Big(\int_I\|N'(s)\|^2ds\Big)^{1/2}\le\frac{2n}{W}\Big(\int_J\|N(s)\|^2ds\Big)^{1/2}.
--   $$
--   The same inequality holds for $\mathbb R^d$ with the variance seminorm $\|\cdot\|_p$ of any fixed probability vector $p$.
--
--   This lets the derivative energy of a sum of $n$ exponentials on a window's middle third be paid for by its position energy on the whole window, whatever the exponents.
--
--   Differences from the source:
--   - generalization: K a real Hilbert space → K a real inner product space, not assumed complete; reason: only norms of finite sums and of their derivatives occur; every Hilbert space is an instance
--   - generalization: the seminorm clause on ℝⁿ, n also the number of terms → ℝᵈ for every d, independent of n; reason: the argument never uses d = n; d = n is the printed case
--   - encoding: (∫_I ‖·‖_p² ds)^{1/2} → Real.sqrt of the integral of var p; reason: ‖·‖_p² is Var_p by definition
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma 5.2, (36), p.19

import Mathlib
import Definitions.Def_OptHedgeGames_Notation

namespace OptHedgeGames

universe u

/-- **Lemma 5.2** (interior Bernstein inequality, `L²` form; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma 5.2, p.19). Let `K` be a
real Hilbert space, let `N(s) = Σ_{k=1}^n wₖ e^{λₖs}` with `wₖ ∈ K` and `λₖ ∈ ℝ`, and let
`I = [α + W, α + 2W]` be the middle third of `J = [α, α + 3W]` for some `α ∈ ℝ` and `W > 0`. Then
`(∫_I ∥N′(s)∥² ds)^{1/2} ≤ (2n/W) (∫_J ∥N(s)∥² ds)^{1/2}`, which is (36). The same inequality holds
for `ℝᵈ` equipped with the variance seminorm `∥·∥_p` of any fixed probability vector `p`.

**Formalization Note** `K` is a real inner product space, with no completeness: only norms of finite
sums and of their derivatives occur, and a Hilbert space is an instance. The seminorm clause holds
for every dimension `d`, independent of the number `n` of terms; `d = n` is the printed case. `∥·∥²_p`
is written `var p`. `N′` is `deriv N`, and `N` is smooth. -/
theorem lemma_5_2 :
    (∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℝ K] (n : ℕ) (w : Fin n → K)
      (lam : Fin n → ℝ) (N : ℝ → K), (∀ s, N s = ∑ k, Real.exp (lam k * s) • w k) →
      ∀ α W : ℝ, 0 < W →
        Real.sqrt (∫ s in (α + W)..(α + 2 * W), ‖deriv N s‖ ^ 2) ≤
          2 * (n : ℝ) / W * Real.sqrt (∫ s in α..(α + 3 * W), ‖N s‖ ^ 2)) ∧
    (∀ (d n : ℕ) (p : Fin d → ℝ), p ∈ stdSimplex ℝ (Fin d) →
      ∀ (w : Fin n → Fin d → ℝ) (lam : Fin n → ℝ) (N : ℝ → Fin d → ℝ),
      (∀ s, N s = ∑ k, Real.exp (lam k * s) • w k) →
      ∀ α W : ℝ, 0 < W →
        Real.sqrt (∫ s in (α + W)..(α + 2 * W), var p (deriv N s)) ≤
          2 * (n : ℝ) / W * Real.sqrt (∫ s in α..(α + 3 * W), var p (N s))) := by sorry

end OptHedgeGames
