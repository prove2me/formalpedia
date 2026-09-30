-- Prove2me | Theorems.Thm_NonuniformCompetitive_Triangle345_lp_lower_bound
-- name    : NonuniformCompetitive.Triangle345.lp_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:57:36.360861+00:00
-- url     : https://prove2.me/theorems/d438e2a6-9b97-4ca7-beca-f360db9200d5
-- title:
--   §5, p. 568 — the twelve phase constraints of the 3-4-5 triangle force $\alpha \ge 1652/1069$
-- statement:
--   This is the linear-programming lower bound in the proof of Theorem 13 of Karlin, Manasse, McGeoch and Owicki for the two-server problem on the triangle with points $a,b,c$ and distances $d(ab)=3$, $d(ac)=5$, $d(bc)=4$.
--
--   A phase-based randomized algorithm $A$ is described by nine probabilities $\pi_1,\dots,\pi_9$: after a given prefix of a phase, $\pi_i$ is the probability that $A$ occupies a given configuration (the second table on p. 567 of the paper). A potential $\Phi_{ab},\Phi_{ac},\Phi_{bc}$ is attached to each configuration of the two servers, and $\alpha$ is the LP bound. Each of the twelve possible phases, starting in configuration $s$ and ending in configuration $s'$, gives the constraint
--   $$\text{A's expected cost} \le \alpha\cdot(\text{opt's cost}) + \Phi_s - \Phi_{s'}.$$
--   Concretely, the twelve constraints are
--   1. $8-4\pi_1 \le 4\alpha+\Phi_{ab}-\Phi_{ac}$ (phase $\{a,b\}$, requests $ca$);
--   2. $16+2\pi_1-4\pi_2-2\pi_3-4\pi_4 \le 8\alpha+\Phi_{ab}-\Phi_{ab}$ (requests $cbaba$);
--   3. $14+2\pi_1-4\pi_2-2\pi_3+6\pi_4-4\pi_5 \le 12\alpha+\Phi_{ab}-\Phi_{ac}$ (requests $cbabca$);
--   4. $11+2\pi_1-4\pi_2-2\pi_3+6\pi_4+2\pi_5 \le 11\alpha+\Phi_{ab}-\Phi_{bc}$ (requests $cbabcb$);
--   5. $8+2\pi_1-4\pi_2+6\pi_3 \le 8\alpha+\Phi_{ab}-\Phi_{ac}$ (requests $cbac$);
--   6. $5+2\pi_1+6\pi_2 \le 5\alpha+\Phi_{ab}-\Phi_{bc}$ (requests $cbc$);
--   7. $10-4\pi_6-2\pi_7 \le 4\alpha+\Phi_{ac}-\Phi_{ab}$ (phase $\{a,c\}$, requests $bab$);
--   8. $6-4\pi_6+6\pi_7 \le 6\alpha+\Phi_{ac}-\Phi_{ac}$ (requests $bac$);
--   9. $3+6\pi_6 \le 3\alpha+\Phi_{ac}-\Phi_{bc}$ (requests $bc$);
--   10. $11-2\pi_8-4\pi_9 \le 5\alpha+\Phi_{bc}-\Phi_{ab}$ (phase $\{b,c\}$, requests $aba$);
--   11. $6-2\pi_8+6\pi_9 \le 6\alpha+\Phi_{bc}-\Phi_{bc}$ (requests $abc$);
--   12. $3+6\pi_8 \le 3\alpha+\Phi_{bc}-\Phi_{ac}$ (requests $ac$).
--
--   The claim is that for all real numbers $\pi_1,\dots,\pi_9,\Phi_{ab},\Phi_{ac},\Phi_{bc},\alpha$ satisfying these twelve inequalities,
--   $$\alpha \ge \frac{1652}{1069}.$$
--
--   Together with Theorem 3 of the paper (a lower bound on the LP bound of phase-based algorithms is a lower bound on the competitive factor of every algorithm), this is the source of the lower bound in Theorem 13.
--
--   **Formalization Note** All thirteen variables are free real numbers, exactly as the paper permits ("we can permit the probabilities and potentials to be free variables"); no constraint $0\le\pi_i\le1$ is imposed, which makes the statement stronger than the boxed one. The constraints are written out one per hypothesis, in the order of the table on p. 568; the self-loop phases 2, 8, 11 keep the literal $\Phi_s-\Phi_s$ term.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 568, §5 (proof of Theorem 13): table of A's costs and the LP minimum α = 1652/1069; phases from the first table on p. 567

import Mathlib

namespace NonuniformCompetitive.Triangle345

/-- Karlin–Manasse–McGeoch–Owicki (Algorithmica 11, 1994), §5, p. 568: the phase LP for the
two-server problem on the triangle with `d(ab) = 3`, `d(ac) = 5`, `d(bc) = 4`.
The variables `π₁, …, π₉` (the probabilities of the second table of p. 567), the potentials
`Φab, Φac, Φbc` of the three configurations and the ratio `α` are free real numbers (no `[0,1]`
box, as the paper permits). Each hypothesis `hᵢ` is the constraint of the `i`-th phase of the
table on p. 568, `A's cost ≤ α · opt's cost + Φ_initial − Φ_final`.
Minimizing `α` subject to these twelve constraints gives `1652/1069`, so every feasible `α` is at
least `1652/1069`. -/
theorem lp_lower_bound (π₁ π₂ π₃ π₄ π₅ π₆ π₇ π₈ π₉ Φab Φac Φbc α : ℝ)
    -- phase 1: {a,b}, requests ca, final {a,c}, opt 4
    (h1 : 8 - 4 * π₁ ≤ 4 * α + Φab - Φac)
    -- phase 2: {a,b}, requests cbaba, final {a,b}, opt 8
    (h2 : 16 + 2 * π₁ - 4 * π₂ - 2 * π₃ - 4 * π₄ ≤ 8 * α + Φab - Φab)
    -- phase 3: {a,b}, requests cbabca, final {a,c}, opt 12
    (h3 : 14 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ - 4 * π₅ ≤ 12 * α + Φab - Φac)
    -- phase 4: {a,b}, requests cbabcb, final {b,c}, opt 11
    (h4 : 11 + 2 * π₁ - 4 * π₂ - 2 * π₃ + 6 * π₄ + 2 * π₅ ≤ 11 * α + Φab - Φbc)
    -- phase 5: {a,b}, requests cbac, final {a,c}, opt 8
    (h5 : 8 + 2 * π₁ - 4 * π₂ + 6 * π₃ ≤ 8 * α + Φab - Φac)
    -- phase 6: {a,b}, requests cbc, final {b,c}, opt 5
    (h6 : 5 + 2 * π₁ + 6 * π₂ ≤ 5 * α + Φab - Φbc)
    -- phase 7: {a,c}, requests bab, final {a,b}, opt 4
    (h7 : 10 - 4 * π₆ - 2 * π₇ ≤ 4 * α + Φac - Φab)
    -- phase 8: {a,c}, requests bac, final {a,c}, opt 6
    (h8 : 6 - 4 * π₆ + 6 * π₇ ≤ 6 * α + Φac - Φac)
    -- phase 9: {a,c}, requests bc, final {b,c}, opt 3
    (h9 : 3 + 6 * π₆ ≤ 3 * α + Φac - Φbc)
    -- phase 10: {b,c}, requests aba, final {a,b}, opt 5
    (h10 : 11 - 2 * π₈ - 4 * π₉ ≤ 5 * α + Φbc - Φab)
    -- phase 11: {b,c}, requests abc, final {b,c}, opt 6
    (h11 : 6 - 2 * π₈ + 6 * π₉ ≤ 6 * α + Φbc - Φbc)
    -- phase 12: {b,c}, requests ac, final {a,c}, opt 3
    (h12 : 3 + 6 * π₈ ≤ 3 * α + Φbc - Φac) :
    (1652 / 1069 : ℝ) ≤ α := by sorry

end NonuniformCompetitive.Triangle345
