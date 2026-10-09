-- Prove2me | Theorems.Thm_OnlineCombOpt_Exp2LB_theorem_1
-- name    : OnlineCombOpt.Exp2LB.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:58.753508+00:00
-- url     : https://prove2.me/theorems/2bd3e4a1-a134-4fe9-96ec-dcce15972539
-- title:
--   Theorem 1, p. 6 — EXP2 has full-information regret at least 0.01 d^{3/2}√n on some action set, for every η
-- statement:
--   Consider online combinatorial optimization with full information: at each round $t=1,\dots,n$ the player draws an action $a_t$ from a finite set $\mathcal A\subseteq\{0,1\}^d$ whose elements all have the same number $m$ of ones, the adversary chooses a loss vector $z_t\in[0,1]^d$, and the player pays $a_t^\top z_t$ and then observes $z_t$. The regret is $R_n=\mathbb E\sum_{t=1}^n a_t^\top z_t-\min_{a\in\mathcal A}\sum_{t=1}^n a^\top z_t$.
--
--   **Theorem.** Let $n\ge d$, with $d$ a multiple of $4$. There is a nonempty set $\mathcal A\subseteq\{0,1\}^d$ with $\|a\|_1=m$ for all $a\in\mathcal A$ (for some $m$) such that, for every learning rate $\eta\ge 0$, there is an adversary $z_1,\dots,z_n\in[0,1]^d$ against which the exponentially weighted forecaster EXP2 (Figure 2) with learning rate $\eta$ has regret
--   $$R_n\;\ge\;0.01\,d^{3/2}\sqrt n .$$
--
--   Since online mirror descent with the negative entropy achieves regret of order $m\sqrt{n\log(d/m)}$, which for this $\mathcal A$ (with $m=d/2$) is of order $d\sqrt n$, the theorem shows that EXP2 is suboptimal by a factor $\sqrt d$ for every choice of its learning rate. It answers a question of Koolen, Warmuth and Kivinen.
--
--   **Formalization Note** The order of quantifiers is the paper's: $\mathcal A$ is chosen before $\eta$, and the adversary after $\eta$. The hypothesis "$d$ a multiple of $4$" is the proof's own simplifying assumption (App. A, p. 14), added because the printed statement is false for $d=1$: every $\mathcal A\subseteq\{0,1\}^1$ with constant norm is a singleton, so the regret is $0$. The parity of $n$, also assumed in App. A, is not added. The adversary is exhibited as a deterministic, oblivious loss sequence with values in $[0,1]^d$; this is a special case of the paper's adaptive adversaries, so the existential is at least as strong as the paper's $\sup_{\text{adversary}}$. Against such an adversary the expectation in $R_n$ is the finite sum $\sum_t\sum_a p_t(a)\,a^\top z_t$. $\eta=0$ (uniform play) is included. $d^{3/2}$ is $d\sqrt d$, and $0.01$ is the real $1/100$.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 6, Theorem 1 (proof in App. A, pp. 14–16)

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset

namespace OnlineCombOpt.Exp2LB

/-- Theorem 1 (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2, p. 6): let `n ≥ d` (with `d` a multiple
of 4). There is an action set `A ⊆ {0,1}^d` with constant `‖a‖₁` such that, for every learning rate
`η ≥ 0`, some adversary with losses in `[0,1]^d` forces full-information EXP2 to regret
`R_n ≥ 0.01 d^{3/2} √n`. -/
theorem theorem_1 (n d : ℕ) (hd : 4 ∣ d) (hnd : d ≤ n) :
    ∃ (A : Finset (Fin d → ℝ)) (m : ℕ), IsBinaryActionSet A m ∧
      ∀ η : ℝ, 0 ≤ η → ∃ z : ℕ → Fin d → ℝ, (∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) ∧
        (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤ exp2Regret A η z n := by sorry

end OnlineCombOpt.Exp2LB
