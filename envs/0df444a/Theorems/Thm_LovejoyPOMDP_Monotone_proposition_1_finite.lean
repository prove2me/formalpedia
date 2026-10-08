-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_proposition_1_finite
-- name    : LovejoyPOMDP.Monotone.proposition_1_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:51.116218+00:00
-- url     : https://prove2.me/theorems/e1e93c05-d1f3-4a67-8a11-b3b6da3717b8
-- title:
--   Proposition 1, part 1 — V*_t is nondecreasing on (Π(S), ≥r) for t = 1, …, N + 1
-- statement:
--   Consider a finite POMDP as in §2 of the paper with horizon $N<\infty$ and salvage value $g_s$. Assume
--
--   1. (a) $g_s$ is nondecreasing on $S$;
--   2. (b) $g(\cdot,a)$ is nondecreasing on $S$ for each $a\in A$;
--   3. (c) $P^a$ is $\mathrm{TP}_2$ for each $a\in A$;
--   4. (d) $r^a(j)\ge_r r^a(j')$ for $j\ge j'$ in $S$ and $a\in A$.
--
--   Then for $t=1,2,\dots,N+1$ and all $\pi,\pi'\in\Pi(S)$,
--   $$\pi\ge_r\pi'\ \Longrightarrow\ V^*_t(\pi)\ \ge\ V^*_t(\pi'),$$
--   where $V^*_t$ are the optimal value functions of the recursion (3).
--
--   So a decision maker who is more confident, in the MLR sense, that the system is in a high state expects a higher optimal value. This monotonicity is the input to Proposition 2.
--
--   **Formalization Note** $V^*_t$ is `M.Vstar gs N t`, computed by the steps-to-go recursion; the range $1\le t\le N+1$ includes the salvage stage $t=N+1$.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Proposition 1, part 1

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Proposition 1, part 1 (`N < ∞`).

If (a) `g_s` is nondecreasing on `S`, (b) `g(·, a)` is nondecreasing on `S` for each `a ∈ A`,
(c) `P^a` is TP₂ for each `a ∈ A`, and (d) `r^a(j) ≥r r^a(j')` for `j ≥ j'` in `S`, `a ∈ A`, then for
`t = 1, 2, …, N + 1`, `π ≥r π'` in `Π(S)` implies `V*_t(π) ≥ V*_t(π')`.

**Formalization Note.** `M.Vstar gs N t` is `V*_t` of the recursion (3) with horizon `N` and
salvage `g_s` (`V*_{N+1}(π) = Σ_i π_i g_s(i)`). -/
theorem proposition_1_finite {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (gs : S → ℝ) (hgs : Monotone gs)
    (hg : ∀ a, Monotone (fun i => M.g i a))
    (hP : ∀ a, TP2 (M.P a))
    (hR : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (N t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ N + 1)
    {π π' : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (hπ' : π' ∈ stdSimplex ℝ S) (h : MLRGE π π') :
    M.Vstar gs N t π' ≤ M.Vstar gs N t π := by sorry

end LovejoyPOMDP.Monotone
