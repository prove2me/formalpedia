-- Prove2me | Theorems.Thm_OnlineConvexOpt_GamesDuality_simple_lp_regret_v2
-- name    : OnlineConvexOpt.GamesDuality.simple_lp_regret_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:23:12.168197+00:00
-- url     : https://prove2.me/theorems/6b387766-bfce-41e2-b4a4-6f8aa42b1a89
-- title:
--   Lemma 8.4 — Algorithm 28 computes a $\sqrt{2\log n}/\sqrt T$-approximate game solution (corrected $\lambda_R$)
-- statement:
--   **Statement (Lemma 8.4).** Let $A\in\mathbb R^{n\times m}$ with $|A_{ij}|\le1$, $n,m\ge1$, $T\ge1$, and let $(x,y)$ be a run of Algorithm 28 on $A$ with learning rate $\eta=\sqrt{2\log n/T}$. Let $\bar x=\frac1T\sum_{t=0}^{T-1}x_t$ be the returned vector. Then for every column strategy $y'\in\Delta_m$,
--   $$\bar x^\top Ay'\;\le\;\lambda_R(A)+\frac{\sqrt{2\log n}}{\sqrt T},\qquad \lambda_R(A)=\min_{x\in\Delta_n}\max_{y\in\Delta_m}x^\top Ay ,$$
--   i.e. $\bar x$ is a $\sqrt{2\log n}/\sqrt T$-approximate solution of the game (and of the linear program it encodes), with $\lambda^\star=\lambda_C=\lambda_R$ (Theorem 8.3) rendered as $\lambda_R$.
--
--   **Formalization Note.** The retired statement used `lambdaR` from `OnlineConvexOpt_GamesDuality_Game`, defined with the binders `⨅ x ∈ Δn, ⨆ y ∈ Δm`, which on $\mathbb R$ collapse to the junk value $0$ for every matrix (inner infima/suprema over empty index types). The new statement imports `OnlineConvexOpt_GamesDuality_Game_v2`, where $\lambda_R$ is the real infimum over $x\in\Delta_n$ of the real supremum over $y\in\Delta_m$ of $x^\top Ay$ (images of the nonempty compact simplices, hence genuine min/max). All other hypotheses are unchanged.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 147, Lemma 8.4 (PDF p. 169)

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game_v2

namespace OnlineConvexOpt.GamesDuality

/-- **Lemma 8.4**, Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 147: the vector `x̄` returned by Algorithm 28 after `T` rounds is a
`√(2 log n) / √T`-approximate solution to the zero-sum game (and the linear program it
describes) — meaning `max_{y ∈ Δm} x̄⊤Ay ≤ λ⋆ + √(2 log n)/√T`, rendering the book's
`λ⋆ = λ_C = λ_R` (Theorem 8.3) as `λ_R`.

Corrected version: `lambdaR` is now the `OnlineConvexOpt_GamesDuality_Game_v2` value
`min_{x∈Δn} max_{y∈Δm} x⊤Ay` (genuine extrema over the nonempty compact simplices); the retired
definition's `⨅ x ∈ Δn, ⨆ y ∈ Δm` binders collapsed to the junk value `0` for every matrix. -/
theorem simple_lp_regret_v2 {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y) :
    ∀ y' ∈ stdSimplex ℝ (Fin m),
      rowValue A (average x T) y' ≤
        lambdaR A + Real.sqrt (2 * Real.log (n : ℝ)) / Real.sqrt (T : ℝ) := by sorry

end OnlineConvexOpt.GamesDuality
