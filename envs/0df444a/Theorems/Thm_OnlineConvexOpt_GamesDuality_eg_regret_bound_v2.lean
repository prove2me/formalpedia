-- Prove2me | Theorems.Thm_OnlineConvexOpt_GamesDuality_eg_regret_bound_v2
-- name    : OnlineConvexOpt.GamesDuality.eg_regret_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:56.1457+00:00
-- url     : https://prove2.me/theorems/845adfb0-7493-49e4-8c42-d49059b1adaa
-- title:
--   Eq. (8.1) — Exponentiated-gradient regret of the row player in Algorithm 28 (genuine simplex comparator)
-- statement:
--   **Statement (Eq. (8.1)).** Let $A\in\mathbb R^{n\times m}$ with $|A_{ij}|\le1$, $n,m\ge1$, $T\ge1$, and let $(x,y)$ be a run of Algorithm 28 on $A$ with learning rate $\eta=\sqrt{2\log n/T}$: the row player starts uniform and updates by the exponentiated-gradient rule on the linear loss $x\mapsto x^\top Ay_t$ while the column player best-responds every round. Then
--   $$\sum_{t=0}^{T-1}x_t^\top Ay_t\;\le\;\min_{x'\in\Delta_n}\sum_{t=0}^{T-1}(x')^\top Ay_t+\sqrt{2T\log n}.$$
--
--   **Formalization Note.** The retired statement wrote the comparator as `⨅ x' ∈ stdSimplex ℝ (Fin n), …`, which on $\mathbb R$ evaluates to the junk value $0$ at every $x'\notin\Delta_n$, so the comparator was $\le0$ and the claim failed for $A=[1]$. The comparator is now the real infimum of the image of $\Delta_n$ under the cumulative loss, a genuine (attained) minimum since $\Delta_n$ is nonempty and compact for $n\ge1$ and the loss is continuous. The constant $\sqrt{2T\log n}$ with $\eta=\sqrt{2\log n/T}$ is the Hedge/multiplicative-weights bound for losses with entries in $[-1,1]$ (Hoeffding's lemma with range $2$: regret $\le \eta T/2+\log n/\eta$), the "appropriate choice of $\eta$" the book invokes; the run predicate `IsSimpleLPRun` is from the re-issued `OnlineConvexOpt_GamesDuality_Game_v2` (unchanged except for the corrected $\lambda_R,\lambda_C$). Rounds are $0$-indexed.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 145, Eq. (8.1) (PDF p. 167)

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game_v2

namespace OnlineConvexOpt.GamesDuality

/-- **Eq. (8.1)**, Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 145: the row player's cumulative value against Algorithm 28's run
`(x, y)` on `T` rounds is within `√(2T log n)` of the best fixed row strategy's cumulative
value, for the learning rate `η = √(2 log n / T)` (the exponentiated gradient / multiplicative
weights regret bound specialized to this run's linear losses `f_t(x) = x⊤A y_t`, with
`|A_ij| ≤ 1`, on the simplex). The comparator is the genuine minimum over the simplex `Δn`
(nonempty and compact for `n ≥ 1`), written as the real infimum of the image of `Δn`.

Corrected version: the retired statement wrote the comparator as the bounded binder
`⨅ x' ∈ stdSimplex ℝ (Fin n), …`, which on `ℝ` evaluates to the junk value `sInf ∅ = 0` at every
`x' ∉ Δn` and so was `≤ 0` for every matrix. -/
theorem eg_regret_bound_v2 {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y) :
    ∑ t ∈ Finset.range T, rowValue A (x t) (y t) ≤
      sInf ((fun x' => ∑ t ∈ Finset.range T, rowValue A x' (y t)) '' stdSimplex ℝ (Fin n)) +
        Real.sqrt (2 * (T : ℝ) * Real.log (n : ℝ)) := by sorry

end OnlineConvexOpt.GamesDuality
