-- Prove2me | Theorems.Thm_NonuniformCompetitive_Triangle345_lp_attained
-- name    : NonuniformCompetitive.Triangle345.lp_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:58:31.068376+00:00
-- url     : https://prove2.me/theorems/fd67daab-72b9-427c-aedf-b7a92c9e08e0
-- title:
--   §5, p. 568 — the printed probabilities meet all twelve phase constraints at $\alpha = 1652/1069$
-- statement:
--   This is the attainment half of the linear program in the proof of Theorem 13 of Karlin, Manasse, McGeoch and Owicki (two servers on the triangle with $d(ab)=3$, $d(ac)=5$, $d(bc)=4$).
--
--   Take the probabilities determined by the minimization,
--   $$\pi_1=\tfrac{2161}{3207},\ \pi_2=\tfrac{169}{1069},\ \pi_3=\tfrac{1481}{3207},\ \pi_4=\tfrac{2749}{3207},\ \pi_5=\tfrac{1016}{3207},\ \pi_6=\tfrac{371}{1069},\ \pi_7=\tfrac{2491}{3207},\ \pi_8=\tfrac{212}{1069},\ \pi_9=\tfrac{1961}{3207},$$
--   and $\alpha = 1652/1069$. In the paper, $\pi_i$ is the probability that the algorithm occupies a given configuration after a given prefix of a phase (second table of p. 567): starting from $\{a,b\}$, after $c$ the algorithm is in $\{a,c\}$ with probability $\pi_1$ and in $\{b,c\}$ with probability $1-\pi_1$; after $cb$ in $\{a,b\}$ with probability $\pi_2$; after $cba$ in $\{a,b\}$ with probability $\pi_3$ (otherwise $\{a,c\}$); after $cbab$ in $\{a,b\}$ with probability $\pi_4$; after $cbabc$ in $\{a,c\}$ with probability $\pi_5$; starting from $\{a,c\}$, after $b$ in $\{a,b\}$ with probability $\pi_6$ and after $ba$ with probability $\pi_7$; starting from $\{b,c\}$, after $a$ in $\{a,b\}$ with probability $\pi_8$ and after $ab$ with probability $\pi_9$.
--
--   The claim is:
--   1. each $\pi_i$ lies in $[0,1]$, so these are genuine probabilities;
--   2. there exist real potentials $\Phi_{ab},\Phi_{ac},\Phi_{bc}$ such that all twelve phase constraints
--   $$\text{A's expected cost} \le \alpha\cdot(\text{opt's cost}) + \Phi_s - \Phi_{s'}$$
--   of the table on p. 568 hold at these values (the constraints are listed one by one in the companion milestone on the LP lower bound).
--
--   Together with Theorem 2 of the paper (an LP bound of $\alpha$ for a lazy phase-based algorithm makes it $\alpha$-competitive), this is the source of the upper bound in Theorem 13.
--
--   **Formalization Note** The paper names no potentials, so they are existentially quantified. The printed probability values are fixed by `let` bindings.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 568, §5 (proof of Theorem 13): the values π₁, …, π₉ determined in the minimization and the table of A's costs

import Mathlib

namespace NonuniformCompetitive.Triangle345

/-- Karlin–Manasse–McGeoch–Owicki (Algorithmica 11, 1994), §5, p. 568: the probabilities
determined by the minimization, `π₁ = 2161/3207`, `π₂ = 169/1069`, `π₃ = 1481/3207`,
`π₄ = 2749/3207`, `π₅ = 1016/3207`, `π₆ = 371/1069`, `π₇ = 2491/3207`, `π₈ = 212/1069`,
`π₉ = 1961/3207`, all lie in `[0,1]`, and together with suitable potentials `Φab, Φac, Φbc` they
satisfy all twelve phase constraints of the table on p. 568 at `α = 1652/1069`
(each constraint reads `A's cost ≤ α · opt's cost + Φ_initial − Φ_final`). -/
theorem lp_attained :
    let π₁ : ℝ := 2161 / 3207
    let π₂ : ℝ := 169 / 1069
    let π₃ : ℝ := 1481 / 3207
    let π₄ : ℝ := 2749 / 3207
    let π₅ : ℝ := 1016 / 3207
    let π₆ : ℝ := 371 / 1069
    let π₇ : ℝ := 2491 / 3207
    let π₈ : ℝ := 212 / 1069
    let π₉ : ℝ := 1961 / 3207
    let α : ℝ := 1652 / 1069
    (0 ≤ π₁ ∧ π₁ ≤ 1) ∧ (0 ≤ π₂ ∧ π₂ ≤ 1) ∧ (0 ≤ π₃ ∧ π₃ ≤ 1) ∧
    (0 ≤ π₄ ∧ π₄ ≤ 1) ∧ (0 ≤ π₅ ∧ π₅ ≤ 1) ∧ (0 ≤ π₆ ∧ π₆ ≤ 1) ∧
    (0 ≤ π₇ ∧ π₇ ≤ 1) ∧ (0 ≤ π₈ ∧ π₈ ≤ 1) ∧ (0 ≤ π₉ ∧ π₉ ≤ 1) ∧
    ∃ Φab Φac Φbc : ℝ,
      -- phase 1: {a,b}, requests ca, final {a,c}, opt 4
      8 - 4 * π₁ ≤ 4 * α + Φab - Φac ∧
      -- phase 2: {a,b}, requests cbaba, final {a,b}, opt 8
      16 + 2 * π₁ - 4 * π₂ - 2 * π₃ - 4 * π₄ ≤ 8 * α + Φab - Φab ∧
      -- phase 3: {a,b}, requests cbabca, final {a,c}, opt 12
      14 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ - 4 * π₅ ≤ 12 * α + Φab - Φac ∧
      -- phase 4: {a,b}, requests cbabcb, final {b,c}, opt 11
      11 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ + 2 * π₅ ≤ 11 * α + Φab - Φbc ∧
      -- phase 5: {a,b}, requests cbac, final {a,c}, opt 8
      8 + 2 * π₁ - 4 * π₂ + 6 * π₃ ≤ 8 * α + Φab - Φac ∧
      -- phase 6: {a,b}, requests cbc, final {b,c}, opt 5
      5 + 2 * π₁ + 6 * π₂ ≤ 5 * α + Φab - Φbc ∧
      -- phase 7: {a,c}, requests bab, final {a,b}, opt 4
      10 - 4 * π₆ - 2 * π₇ ≤ 4 * α + Φac - Φab ∧
      -- phase 8: {a,c}, requests bac, final {a,c}, opt 6
      6 - 4 * π₆ + 6 * π₇ ≤ 6 * α + Φac - Φac ∧
      -- phase 9: {a,c}, requests bc, final {b,c}, opt 3
      3 + 6 * π₆ ≤ 3 * α + Φac - Φbc ∧
      -- phase 10: {b,c}, requests aba, final {a,b}, opt 5
      11 - 2 * π₈ - 4 * π₉ ≤ 5 * α + Φbc - Φab ∧
      -- phase 11: {b,c}, requests abc, final {b,c}, opt 6
      6 - 2 * π₈ + 6 * π₉ ≤ 6 * α + Φbc - Φbc ∧
      -- phase 12: {b,c}, requests ac, final {a,c}, opt 3
      3 + 6 * π₈ ≤ 3 * α + Φbc - Φac := by sorry

end NonuniformCompetitive.Triangle345
