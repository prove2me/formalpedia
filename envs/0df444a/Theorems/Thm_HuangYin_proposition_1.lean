-- Prove2me | Theorems.Thm_HuangYin_proposition_1
-- name    : HuangYin.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:07.235178+00:00
-- url     : https://prove2.me/theorems/e6ce5966-d4bf-4575-9803-73635acfb0a9
-- title:
--   Proposition 1 — the optimal selling policy when $K=1$ (corrected: $c_L\le v_{HL}$ in (i), (ii))
-- statement:
--   Consider the two-period model with one anecdote per customer ($K=1$). Optimality is over every feasible policy: every opaque policy with $\xi_1,\xi_2\in[0,1]$, $p_1\le v_{HL}$ and any $p_2$, and every transparent policy.
--
--   1. If $c_L\le v_{HL}$, $0\le\alpha<\frac{\sqrt{17}-3}{2}$, $\frac{v_{HL}-c_L}{c_H-c_L}<\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2}$ and $\frac{(1-\alpha)(v_{HL}-c_L)^2}{(4-4\alpha-\alpha^2)(c_H-c_L)}>\max\{v_H-c_H,v_L-c_L\}$, it is optimal to use probabilistic selling with
--   $$p_1^*=p_2^*=v_{HL},\quad \xi_1^*=\frac{(2-\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)},\quad \xi_2^*=\frac{(2-3\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)},\quad \Pi^*=\frac{2(1-\alpha)(v_{HL}-c_L)^2}{(4-4\alpha-\alpha^2)(c_H-c_L)}.$$
--   2. If $c_L\le v_{HL}$, $\frac{\sqrt{17}-3}{2}\le\alpha\le1$, $\frac{v_{HL}-c_L}{c_H-c_L}<\frac{2}{1+\alpha}$ and $\frac{(1+\alpha)^2(v_{HL}-c_L)^2}{8(c_H-c_L)}>\max\{v_H-c_H,v_L-c_L\}$, it is optimal to use probabilistic selling with
--   $$p_1^*=p_2^*=v_{HL},\quad \xi_1^*=\frac{(1+\alpha)(v_{HL}-c_L)}{2(c_H-c_L)},\quad \xi_2^*=0,\quad \Pi^*=\frac{(1+\alpha)^2(v_{HL}-c_L)^2}{4(c_H-c_L)}.$$
--   3. Otherwise, if $v_H-c_H\ge v_L-c_L$ it is optimal to sell product $H$ transparently at $p_1^*=p_2^*=v_H$, with $\Pi^*=2(v_H-c_H)$; if $v_L-c_L\ge v_H-c_H$ it is optimal to sell product $L$ transparently at $p_1^*=p_2^*=v_L$, with $\Pi^*=2(v_L-c_L)$.
--
--   This is the paper's main result for the basic model: probabilistic selling pays only when both products' transparent margins are low, and then the firm prices at $v_{HL}$ and lowers the probability of $H$ in the second period, where word of mouth from the first period carries part of the signal.
--
--   Differences from the source:
--
--   - correction: no sign condition on vHL − cL → hypothesis cL ≤ vHL in clauses (i) and (ii) (clause (iii) carries none); reason: false as printed: α = 0, vH = 3, vL = 1, cH = 6, cL = 5 satisfy every assumption of the paper and lie in region (i), where the printed ξ1* = ξ2* = −3/2 lie outside [0, 1] and Π* = 9/2, while no feasible policy earns more than 0; cL ≤ vHL is exactly ξ1* ≥ 0 and is implied by the vL ≥ cL that the paper's proof uses (p. 30)
--   - encoding: K anecdotes per customer and a prior belief ξ0 (p. 8), with ξ0 = 0 from p. 9 on and K = 1 in §4 → the estimate (ξ0 + anecdote)/(K + 1) with K = 1, ξ0 = 0 built into `estimate`; the purchasing fractions derived from rule (1) in `demand`; reason: §4 and the result fix K = 1 and the paper fixes ξ0 = 0; the derived fractions are Lemma 1's γ's for K = 1 (1 at vL, ξ at vHL, 0 above vHL), so no instance changes
--   - reading: 'the optimal product offering decisions are' / 'it is optimal to use' → the stated choice is feasible and attains the maximum (`OptimalOffer`, `IsOptimal`), not that it is the unique maximizer; reason: Proposition 1 (iii) calls both transparent policies optimal when vH − cH = vL − cL, so optimality cannot mean uniqueness
--   - generalization: opaque prices from the grid {vL, vHL} (Lemma 1, p. 10; §4, p. 11, 'the optimal price in each period should be chosen among the two candidates') → optimality over every opaque policy with any first-period price p1 ≤ vHL and any second-period price p2 ∈ ℝ; reason: the Lean price set contains the grid, so the statement specializes to optimality over the grid
--   - reading: prices p_t chosen freely (§3.2, 'optimizing the price p_t') → first-period opaque price restricted to p1 ≤ vHL; reason: above vHL nobody buys in period 1, yet equation (2) still lets period-2 anecdotes come from period 1 and be H with probability ξ1; with p1 > vHL allowed the result is false (α = 1, vH = 3, vL = 1, cH = 3, cL = 9/10 lies in region (ii) with Π* = 121/210, but p1 > vHL, ξ1 = 1, p2 = vHL, ξ2 = 0 earns 11/10)
--   - generalization: transparent selling of one product, H at pH = vH or L at pL = vL, in both periods (§3.3, p. 11) → transparent policies choosing any product and any price separately in each period; reason: the Lean family contains the paper's two policies; offering both products at once adds nothing because customers are identical
--   - reading: a customer buying product m obtains net utility v_m − p (§3.3) → the whole unit mass buys iff p ≤ v_m; reason: customers buy when their net utility is nonnegative, the same weak inequality as rule (1)
--   - reading: 'the optimal selling policy' among probabilistic and transparent selling → the policy space is the opaque policies and the transparent policies; a policy opaque in one period and transparent in the other is not a policy; reason: the paper defines and compares exactly these two families (§3.2, §3.3, p. 13)
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Proposition 1, p. 13; proof pp. 30–31

import Mathlib
import Definitions.Def_HuangYin_IsOptimal
import Definitions.Def_HuangYin_Region1
import Definitions.Def_HuangYin_Region2

namespace HuangYin

/-- **Proposition 1: the optimal selling policy when `K = 1`** (p. 13), with clauses (i)
and (ii) corrected by the hypothesis `cL ≤ vHL`.
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), Proposition 1, p. 13; proof pp. 30–31.

(i) In `Region1` (`0 ≤ α < (√17 − 3)/2`, `(vHL − cL)/(cH − cL) < (4 − 4α − α²)/(2 − α − α²)`,
`(1 − α)(vHL − cL)²/((4 − 4α − α²)(cH − cL)) > max{vH − cH, vL − cL}`) the probabilistic
selling policy `p1 = p2 = vHL`,
`ξ1 = (2 − α − α²)(vHL − cL)/((4 − 4α − α²)(cH − cL))`,
`ξ2 = (2 − 3α − α²)(vHL − cL)/((4 − 4α − α²)(cH − cL))` is optimal, with profit
`2(1 − α)(vHL − cL)²/((4 − 4α − α²)(cH − cL))`.

(ii) In `Region2` (`(√17 − 3)/2 ≤ α ≤ 1`, `(vHL − cL)/(cH − cL) < 2/(1 + α)`,
`(1 + α)²(vHL − cL)²/(8(cH − cL)) > max{vH − cH, vL − cL}`) the probabilistic selling policy
`p1 = p2 = vHL`, `ξ1 = (1 + α)(vHL − cL)/(2(cH − cL))`, `ξ2 = 0` is optimal, with profit
`(1 + α)²(vHL − cL)²/(4(cH − cL))`.

(iii) Otherwise, if `vH − cH ≥ vL − cL` transparent selling of `H` at `p1 = p2 = vH` is optimal
with profit `2(vH − cH)`, and if `vL − cL ≥ vH − cH` transparent selling of `L` at
`p1 = p2 = vL` is optimal with profit `2(vL − cL)`.

Optimality is over every feasible policy (`IsOptimal`): every opaque policy with
`ξ1, ξ2 ∈ [0,1]`, `p1 ≤ vHL` and any `p2`, and every transparent policy.

**Formalization Note.** The hypothesis `cL ≤ vHL` in clauses (i) and (ii) is a correction: these
clauses are false without it (α = 0, vH = 3, vL = 1, cH = 6, cL = 5 lies in Region1 with
`ξ1 = ξ2 = −3/2` and `Π = 9/2`, while the optimum is `0`). The paper's proof uses `vL ≥ cL`, which
implies it. Clause (iii) does not need it and is stated without it: if `cL > vHL`, every feasible
opaque policy earns at most `0`, and `max{vH − cH, vL − cL} < 0` puts the parameters in Region1 or
Region2. The price space `p1 ≤ vHL`, `p2 ∈ ℝ` contains the paper's grid `{vL, vHL}²`. -/
theorem proposition_1 (P : Params) :
    (P.cL ≤ vHL P → Region1 P →
      IsOptimal P (.opaque (vHL P) (vHL P)
        ((2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))
        ((2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))) ∧
      (Policy.opaque (vHL P) (vHL P)
        ((2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))
        ((2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) /
          ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))).profit P =
        2 * (1 - P.α) * (vHL P - P.cL) ^ 2 / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL))) ∧
    (P.cL ≤ vHL P → Region2 P →
      IsOptimal P (.opaque (vHL P) (vHL P) ((1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL))) 0) ∧
      (Policy.opaque (vHL P) (vHL P)
        ((1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL))) 0).profit P =
        (1 + P.α) ^ 2 * (vHL P - P.cL) ^ 2 / (4 * (P.cH - P.cL))) ∧
    (¬ Region1 P → ¬ Region2 P →
      (P.vL - P.cL ≤ P.vH - P.cH →
        IsOptimal P (.transparent .H .H P.vH P.vH) ∧
        (Policy.transparent .H .H P.vH P.vH).profit P = 2 * (P.vH - P.cH)) ∧
      (P.vH - P.cH ≤ P.vL - P.cL →
        IsOptimal P (.transparent .L .L P.vL P.vL) ∧
        (Policy.transparent .L .L P.vL P.vL).profit P = 2 * (P.vL - P.cL))) := by sorry

end HuangYin
