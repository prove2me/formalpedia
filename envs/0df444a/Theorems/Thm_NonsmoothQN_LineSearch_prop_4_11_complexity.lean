-- Prove2me | Theorems.Thm_NonsmoothQN_LineSearch_prop_4_11_complexity
-- name    : NonsmoothQN.LineSearch.prop_4_11_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:48.987009+00:00
-- url     : https://prove2.me/theorems/d83b3230-903f-4408-ba97-b6720d157579
-- title:
--   Proposition 4.11, pp. 149–150 — convex h: first trial in I between d + 1 and the (corrected) bound
-- statement:
--   Let $h$ be convex on $[0,\infty)$ and satisfy Assumption 4.1 with slope $s<0$, and let $0<c_1<c_2<1$. Then there are $b>0$ and $0<a<\infty$ such that the Armijo–Wolfe steps are exactly the points of the open interval $I=(b,b+a)$ at which $h$ is differentiable. Put
--   $$d=\max\{1+\lfloor\log_2 b\rfloor,0\},\qquad L=\lfloor\log_2(1/a)\rfloor .$$
--   Then Algorithm 4.6 tries a step in $I$, and the number $n+1$ of trials up to and including the first such step satisfies
--   $$d+1\ \le\ n+1\ \le\ \begin{cases} d+1+\max\{d+L,0\}, & d\ge1,\\ 1+\max\{1+L,0\}, & d=0.\end{cases}$$
--
--   The line search therefore reaches the region of Armijo–Wolfe steps after a number of trials logarithmic in $b$ and $1/a$.
--
--   **Formalization Note.** For $d=0$ (that is, $b<1$) the printed upper bound $d+1+\max\{d+L,0\}$ is false: for $s=-1$, $c_1=0.6$, $c_2=0.9$ and $h(t)=-t$ on $[0,\tfrac12]$, $h(t)=-\tfrac12-0.2(t-\tfrac12)$ on $[\tfrac12,10]$, constant afterwards, one has $I=(\tfrac12,1)$, $d=0$, $L=1$, printed bound $2$, but the trials are $1$, $\tfrac12$, $\tfrac34$, and $\tfrac34$ is the first one in $I$ (three trials). The printed proof's claim that $I\subset[2^{d-1},2^d]$ needs $d\ge1$; for $d=0$ the bracket is $[0,1]$, and the bound stated here is the one that bracket gives. The printed bound is kept for $d\ge1$. The case $a=+\infty$ of the paper cannot occur under Assumption 4.1, because boundedness below makes $A$ fail for large $t$. "Tries a step in $I$" is read as "tries a step in the open interval $(b,b+a)$": a trial at a point of nondifferentiability inside it counts.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 149–150, Proposition 4.11 (upper bound corrected for b < 1)

import Mathlib
import Definitions.Def_NonsmoothQN_LineSearch_Basic

open Filter Topology MeasureTheory Set

namespace NonsmoothQN.LineSearch

/-- Proposition 4.11 (complexity of line search, pp. 149–150), with the upper bound corrected
for `b < 1`. For a convex `h` satisfying Assumption 4.1 and `0 < c₁ < c₂ < 1`, the Armijo–Wolfe
steps are the points of an open interval `I = (b, b + a)`, `b > 0`, `0 < a < ∞`, where `h` is
differentiable; with `d = max{1 + ⌊log₂ b⌋, 0}` and `L = ⌊log₂(1/a)⌋`, the first trial in `I` is
trial number `n + 1` (trials counted from 1), where `d + 1 ≤ n + 1`, and
`n + 1 ≤ d + 1 + max{d + L, 0}` if `d ≥ 1`, `n + 1 ≤ 1 + max{1 + L, 0}` if `d = 0`. -/
theorem prop_4_11_complexity (h : ℝ → ℝ) (c₁ c₂ s : ℝ)
    (hconv : ConvexOn ℝ (Set.Ici 0) h)
    (hA41 : Assumption41 h s) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ b a : ℝ, 0 < b ∧ 0 < a ∧
      (∀ t : ℝ, IsAWStep h c₁ c₂ s t ↔ (t ∈ Set.Ioo b (b + a) ∧ DifferentiableAt ℝ h t)) ∧
      ∃ n : ℕ, (lsRun h c₁ c₂ s n).t ∈ Set.Ioo b (b + a) ∧
        (∀ m < n, (lsRun h c₁ c₂ s m).t ∉ Set.Ioo b (b + a)) ∧
        (max (1 + ⌊Real.logb 2 b⌋) 0 + 1 ≤ (n : ℤ) + 1) ∧
        (1 ≤ max (1 + ⌊Real.logb 2 b⌋) 0 →
          (n : ℤ) + 1 ≤ max (1 + ⌊Real.logb 2 b⌋) 0 + 1 +
            max (max (1 + ⌊Real.logb 2 b⌋) 0 + ⌊Real.logb 2 (1 / a)⌋) 0) ∧
        (max (1 + ⌊Real.logb 2 b⌋) 0 = 0 →
          (n : ℤ) + 1 ≤ 1 + max (1 + ⌊Real.logb 2 (1 / a)⌋) 0) := by sorry

end NonsmoothQN.LineSearch
