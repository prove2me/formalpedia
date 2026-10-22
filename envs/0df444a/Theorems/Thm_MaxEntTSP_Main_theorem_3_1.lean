-- Prove2me | Theorems.Thm_MaxEntTSP_Main_theorem_3_1
-- name    : MaxEntTSP.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:25.353894+00:00
-- url     : https://prove2.me/theorems/2a842d9f-7090-4260-96d8-bf6ffff7f816
-- title:
--   Theorem 3.1 — slack vectors for near-minimum cuts
-- statement:
--   On a rooted Held–Karp instance, let $E$ be the LP support outside $e_0$ and $E^*$ an optimal tour through $e_0$. Draw a spanning tree $T$ from the maximum-entropy law with marginals $x$, and put $z=(x+\chi_{E^*})/2$. For $0\le\eta\le10^{-12}$ and $\beta>0$, there are random edge vectors $s$ and $s^*$, determined by $T$, with $s^*\ge0$. For every tree of positive probability they satisfy $s_e\ge-\beta x_e$ on $E$ and, whenever an $\eta$-near minimum cut $S$ has odd $|\delta(S)_T|$,
--   $$s(\delta(S))+s^*(\delta(S))\ge0.$$
--
--   For every optimal-tour edge $e^*$ and LP edge $e$, respectively,
--   $$\mathbb E[s^*_{e^*}]\le218\eta\beta,\qquad\mathbb E[s_e]\le-\tfrac13\varepsilon_P\beta x_e,\quad \varepsilon_P=3.12\cdot10^{-16}.$$
--
--   This is the quantitative payment statement used in the parity-correction bound.
--
--   **Formalization Note** The paper's upper bound on $\eta$ implicitly needs $\eta\ge0$; otherwise the nonnegative $s^*$ would have a negative expected upper bound. The tour is quantified as any optimal tour containing $e_0$.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 18 (PDF 20), Theorem 3.1

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Cuts

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- Main technical theorem, with the nonnegative range of η made explicit. -/
theorem theorem_3_1 (m : ℕ) (hm : 3 ≤ m)
    (c x : Fin m → Fin m → ℝ) (hc : IsMetricCost c) (hx : IsHeldKarp x)
    (a b : Fin m) (hab : a ≠ b) (he0 : x a b = 1) (hcost0 : c a b = 0)
    (π : Equiv.Perm (Fin m)) (hπ : tourCost c π = tspOpt c)
    (hπe0 : pairCost (tourVec π) (s(a, b)) = 1)
    (μ : Finset (Sym2 (Fin m)) → ℝ)
    (hμ : IsMaxEntropy (lpSupport x a b) x μ)
    (η β : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10 ^ 12) (hβ : 0 < β) :
    let E := lpSupport x a b
    let EStar := tourSupport π
    ∃ s sStar : Finset (Sym2 (Fin m)) → Sym2 (Fin m) → ℝ,
      (∀ T e, 0 ≤ sStar T e) ∧
      (∀ T, μ T ≠ 0 → ∀ e ∈ E, -pairCost x e * β ≤ s T e) ∧
      (∀ T, μ T ≠ 0 → ∀ S : Finset (Fin m),
        IsNearMinCut (zVector x π) a b η S → Odd (crossCount T S) →
          0 ≤ randomCutSum s T E S + randomCutSum sStar T EStar S) ∧
      (∀ e ∈ EStar, (∑ T, μ T * sStar T e) ≤ 218 * η * β) ∧
      (∀ e ∈ E, (∑ T, μ T * s T e) ≤
        -(1 / 3 : ℝ) * pairCost x e * epsP * β) := by sorry

end MaxEntTSP.Main
