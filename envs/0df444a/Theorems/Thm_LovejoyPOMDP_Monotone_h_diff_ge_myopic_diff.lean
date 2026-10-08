-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_h_diff_ge_myopic_diff
-- name    : LovejoyPOMDP.Monotone.h_diff_ge_myopic_diff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:17.166787+00:00
-- url     : https://prove2.me/theorems/312022f7-7cb3-480e-9dd6-f6c99e6b2d96
-- title:
--   Proof of Proposition 2, p. 741 — under (a)–(f), h(π, a, V*_{t+1}) − h(π, a′, V*_{t+1}) ≥ Σ_i π_i g(i, a) − Σ_i π_i g(i, a′)
-- statement:
--   Consider a finite POMDP as in §2 of the paper with horizon $N<\infty$, salvage value $g_s$ and a completely ordered action set $A$. Assume (a)–(f) of Proposition 2:
--
--   1. (a) $g_s$ is nondecreasing on $S$;
--   2. (b) $g(\cdot,a)$ is nondecreasing on $S$ for all $a\in A$;
--   3. (c) $P^a\ge_{tp}P^{a'}$ for all $a\ge a'$ in $A$;
--   4. (d) $r^a(j)\ge_r r^a(j')$ for $j\ge j'$ in $S$, all $a\in A$;
--   5. (e) $r^a(j)\ge_s r^{a'}(j)$ for $a\ge a'$ in $A$, all $j\in S$;
--   6. (f) $r^a_{jk}r^{a'}_{j'k}\ge r^{a'}_{jk}r^a_{j'k}$ for $a\ge a'$ in $A$, $j\ge j'$ in $S$, all $k\in O$.
--
--   Then for every $\pi\in\Pi(S)$, all $a\ge a'$ in $A$ and $t=1,2,\dots,N$,
--   $$h(\pi,a,V^*_{t+1})-h(\pi,a',V^*_{t+1})\ \ge\ \sum_{i\in S}\pi_i g(i,a)-\sum_{i\in S}\pi_i g(i,a').$$
--
--   Moving to a larger action gains at least as much in total value as in immediate expected reward. Combined with Lemma 2.2 this yields Proposition 2.
--
--   **Formalization Note** $V^*_{t+1}$ is `M.Vstar gs N (t + 1)` from the recursion (3).
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 741, §5, proof of Proposition 2 (unnumbered display after "Thus,")

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, §5, proof of Proposition 2, p. 741 (unnumbered): "Thus,
`h(π, a, V*_{t+1}) − h(π, a', V*_{t+1}) ≥ Σ_i π_i g(i, a) − Σ_i π_i g(i, a')`".

Under assumptions (a)–(f) of Proposition 2, for any `π ∈ Π(S)`, `a ≥ a'` in `A` and
`t = 1, 2, …, N`, the increment of `h(π, ·, V*_{t+1})` from `a'` to `a` is at least the
increment of the expected one-step reward. -/
theorem h_diff_ge_myopic_diff {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (gs : S → ℝ) (hgs : Monotone gs)
    (hg : ∀ a, Monotone (fun i => M.g i a))
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a'))
    (hRd : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (hRe : ∀ a a' : A, a' ≤ a → ∀ j, StochGE (M.R a j) (M.R a' j))
    (hRf : ∀ a a' : A, a' ≤ a → ∀ j j' : S, j' ≤ j → ∀ k,
      M.R a' j k * M.R a j' k ≤ M.R a j k * M.R a' j' k)
    (N t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ N)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) {a a' : A} (haa' : a' ≤ a) :
    M.myopic π a - M.myopic π a' ≤
      M.hOp π a (M.Vstar gs N (t + 1)) - M.hOp π a' (M.Vstar gs N (t + 1)) := by sorry

end LovejoyPOMDP.Monotone
