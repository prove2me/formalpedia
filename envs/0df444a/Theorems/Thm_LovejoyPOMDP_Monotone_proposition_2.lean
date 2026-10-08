-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_proposition_2
-- name    : LovejoyPOMDP.Monotone.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:08.525978+00:00
-- url     : https://prove2.me/theorems/34547eb4-8104-4029-9b82-9158aa54587a
-- title:
--   Proposition 2 — under (a)–(f) the myopic maximizer bounds every optimal action from below, finite and infinite horizon
-- statement:
--   Consider a finite POMDP as in §2 of the paper, with a completely ordered action set $A$. For a belief $\pi\in\Pi(S)$ let
--   $$\alpha(\pi)=\operatorname{argmax}\Big\{\sum_{i\in S}\pi_i g(i,a) : a\in A\Big\}$$
--   be the set of **myopic** actions. Assume
--
--   1. (a) $g_s$ is nondecreasing on $S$;
--   2. (b) $g(\cdot,a)$ is nondecreasing on $S$ for all $a\in A$;
--   3. (c) $P^a\ge_{tp}P^{a'}$ for all $a\ge a'$ in $A$;
--   4. (d) $r^a(j)\ge_r r^a(j')$ for $j\ge j'$ in $S$, all $a\in A$;
--   5. (e) $r^a(j)\ge_s r^{a'}(j)$ for $a\ge a'$ in $A$, all $j\in S$;
--   6. (f) $r^a_{jk}r^{a'}_{j'k}\ge r^{a'}_{jk}r^a_{j'k}$ for $a\ge a'$ in $A$, $j\ge j'$ in $S$, all $k\in O$.
--
--   Then:
--
--   1. **Finite horizon $N<\infty$.** For all $t=1,\dots,N$ and all $\pi\in\Pi(S)$, let $\delta^*_t(\pi)$ range over the maximizers of $a\mapsto h(\pi,a,V^*_{t+1})$. For every $\delta^*_t(\pi)$ there is an $\alpha(\pi)\le\delta^*_t(\pi)$, and for every $\alpha(\pi)$ there is a $\delta^*_t(\pi)\ge\alpha(\pi)$.
--   2. **Infinite horizon, $0<\beta<1$.** For all $\pi\in\Pi(S)$, let $\delta^*(\pi)$ range over the maximizers of $a\mapsto h(\pi,a,V^*)$, where $V^*$ is the infinite-horizon optimal value. For every $\delta^*(\pi)$ there is an $\alpha(\pi)\le\delta^*(\pi)$, and for every $\alpha(\pi)$ there is a $\delta^*(\pi)\ge\alpha(\pi)$.
--
--   The easily computed myopic policy is thus a lower bound on an optimal policy of the partially observed problem, in both directions of the quantifiers. The ordering of the action set is what makes the bound meaningful.
--
--   **Formalization Note** $V^*_{t+1}$ is `M.Vstar gs N (t + 1)` from the recursion (3) with salvage $g_s$. The infinite-horizon $V^*$ is any `V` with `M.IsBellmanSolution V`, which for $0<\beta<1$ exists and is unique on $\Pi(S)$. The maximizer sets are `argmaxSet`. Hypothesis (a) concerns only the salvage value, so it is attached to part 1 (as `∀ gs, Monotone gs → …`); part 2 does not involve $g_s$. Hypothesis (c) at $a=a'$ makes every $P^a$ $\mathrm{TP}_2$, which is how Proposition 1 enters.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 741, Proposition 2 (with the definition of α(π) above it)

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 741, Proposition 2 (with `α(π)` defined just above it).

Assume (b) `g(·, a)` is nondecreasing on `S` for all `a ∈ A`, (c) `P^a ≥tp P^{a'}` for all
`a ≥ a'` in `A`, (d) `r^a(j) ≥r r^a(j')` for `j ≥ j'` in `S`, all `a ∈ A`, (e) `r^a(j) ≥s r^{a'}(j)`
for `a ≥ a'` in `A`, all `j ∈ S`, and (f) `r^a_{jk} r^{a'}_{j'k} ≥ r^{a'}_{jk} r^a_{j'k}` for
`a ≥ a'` in `A`, `j ≥ j'` in `S`, all `k ∈ O`. Let `α(π)` range over the maximizers of
`a ↦ Σ_i π_i g(i, a)`.

1. `N < ∞`: for every salvage `g_s` satisfying (a) (`g_s` nondecreasing on `S`), all
   `t = 1, …, N` and all `π ∈ Π(S)`: for every maximizer `δ*_t(π)` of `a ↦ h(π, a, V*_{t+1})` there
   is an `α(π) ≤ δ*_t(π)`, and for every `α(π)` there is a `δ*_t(π) ≥ α(π)`.
2. `N = ∞`, `0 < β < 1`: for every bounded solution `V*` of the Bellman equation on `Π(S)` and all
   `π ∈ Π(S)`: for every maximizer `δ*(π)` of `a ↦ h(π, a, V*)` there is an `α(π) ≤ δ*(π)`, and for
   every `α(π)` there is a `δ*(π) ≥ α(π)`.

**Formalization Note.** `V*_{t+1}` is `M.Vstar gs N (t + 1)`, computed by the recursion (3); the
infinite-horizon `V*` is any `V` with `M.IsBellmanSolution V`, which for `0 < β < 1` exists and is
unique on `Π(S)`. Hypothesis (a) concerns only the salvage value, so it is attached to part 1. -/
theorem proposition_2 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hg : ∀ a, Monotone (fun i => M.g i a))
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a'))
    (hRd : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (hRe : ∀ a a' : A, a' ≤ a → ∀ j, StochGE (M.R a j) (M.R a' j))
    (hRf : ∀ a a' : A, a' ≤ a → ∀ j j' : S, j' ≤ j → ∀ k,
      M.R a' j k * M.R a j' k ≤ M.R a j k * M.R a' j' k) :
    (∀ gs : S → ℝ, Monotone gs → ∀ N t : ℕ, 1 ≤ t → t ≤ N → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))),
          ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π),
          ∃ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))), α ≤ d)) ∧
    (0 < M.β → M.β < 1 → ∀ V : (S → ℝ) → ℝ, M.IsBellmanSolution V → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a V), ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π), ∃ d ∈ argmaxSet (fun a => M.hOp π a V), α ≤ d)) := by sorry

end LovejoyPOMDP.Monotone
