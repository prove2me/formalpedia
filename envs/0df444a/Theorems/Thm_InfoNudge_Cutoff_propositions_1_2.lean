-- Prove2me | Theorems.Thm_InfoNudge_Cutoff_propositions_1_2
-- name    : InfoNudge.Cutoff.propositions_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:03.056137+00:00
-- url     : https://prove2.me/theorems/28f3f37e-05c6-4190-a187-e6093f4a7a0d
-- title:
--   Propositions 1–2, p. 16 — an optimal incentive-compatible persuasion mechanism is 1{θ ≤ tʰ} if (15) holds, and otherwise π*_{γᶜ} with γᶜ given by (16)
-- statement:
--   Let a present-biased decision maker have parameters $\beta\in(0,1)$, $\delta\in(0,1]$, $\beta\delta^2C>1$ and a prior $P$ on $[0,1]$ satisfying Assumption 1: $P[\theta\le t^h]>0$ and $P[\theta>t^a]>0$. Then:
--
--   1. **(Proposition 1)** If $E[\theta\mid\theta>t^h]\ge t^a$ (condition (15)), the unconstrained-optimal mechanism $\pi^*_{\gamma^u}(\theta)=1_{\{\theta\le t^h\}}$ is an optimal incentive-compatible persuasion mechanism.
--   2. **(Proposition 2)** If (15) does not hold, there is a $\gamma^c\in(\gamma^u,1)$, where $\gamma^u=F(t^h)$, such that the cutoff mechanism $\pi^*_{\gamma^c}$ of (10) satisfies
--   $$\frac{E[\theta(1-\pi^*_{\gamma^c}(\theta))]}{E[1-\pi^*_{\gamma^c}(\theta)]}=t^a,\qquad(16)$$
--   $\gamma^c$ is the only $\gamma\in[0,1)$ for which $\pi^*_\gamma$ satisfies (16), and $\pi^*_{\gamma^c}$ is an optimal incentive-compatible persuasion mechanism.
--
--   Here a mechanism is optimal if it is incentive-compatible ((6)–(7)) and maximizes $t^hE[\pi(\theta)]-E[\theta\pi(\theta)]$ among **all** incentive-compatible measurable mechanisms $\pi$ with values in $[0,1]$, not only among cutoff mechanisms. Note that $1_{\{\theta\le t^h\}}$ coincides $P$-a.s. with the cutoff mechanism $\pi^*_{\gamma^u}$.
--
--   The result says that the optimal information nudge targets a coherent group: it recommends consuming to the low-risk types and abstaining to the high-risk types, randomizing at most at one atom; when harmful consumption cannot be avoided, the warning to abstain is made exactly as alarming as needed to be credible.
--
--   **Formalization Note** The paper's "the optimal mechanism" is read as "an optimal mechanism", since optima are only unique up to $P$-null sets (and, with an atom at $t^h$, up to the weight on it). Condition (15) and equation (16) are stored cross-multiplied; this is exact because $P[\theta>t^h]>0$ under Assumption 1 and $E[1-\pi^*_\gamma]=1-\gamma>0$ for $\gamma<1$. That $\gamma^c$ exists, lies in $(\gamma^u,1)$ and is unique is part of the conclusion, not an assumption.
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), p. 16, Propositions 1–2, condition (15), eq. (16)

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

namespace InfoNudge.Cutoff

theorem propositions_1_2 (M : Params) (hS : Standing M) (hA : Assumption1 M) :
    (Cond15 M → IsOptimal M (Set.indicator (Set.Iic (th M)) (fun _ => (1 : ℝ)))) ∧
    (¬ Cond15 M →
      ∃ γc ∈ Set.Ioo (F M (th M)) 1,
        Eq16 M γc ∧ (∀ γ ∈ Set.Ico (0 : ℝ) 1, Eq16 M γ → γ = γc) ∧
        IsOptimal M (cutoffMech M γc)) := by sorry

end InfoNudge.Cutoff
