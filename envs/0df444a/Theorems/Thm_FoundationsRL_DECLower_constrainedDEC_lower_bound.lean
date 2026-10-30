-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_constrainedDEC_lower_bound
-- name    : FoundationsRL.DECLower.constrainedDEC_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:20:50.266282+00:00
-- url     : https://prove2.me/theorems/7195c734-c5c8-4369-af9b-3034ea48366d
-- title:
--   Proposition 28 (DEC lower bound) — $\mathbb E[\mathrm{Reg}(T)]\gtrsim\mathrm{dec}^{\mathrm c}_{\varepsilon_T}(\mathcal M)\cdot T$, $\varepsilon_T=c/\sqrt T$
-- statement:
--   There are absolute constants $c_0>0$ and $C>0$ such that the following holds. Let $c\in(0,c_0]$, let $\Pi$ and $\mathcal O$ be measurable decision and observation spaces, and let $\mathcal M$ be a class of models $M:\Pi\to\Delta([0,1]\times\mathcal O)$. Let $T\ge1$ and $\varepsilon_T:=c/\sqrt T$. If
--
--   $$
--   \mathrm{dec}^{\mathrm c}_{\varepsilon_T}(\mathcal M)\ge 10\,\varepsilon_T, \tag{6.30}
--   $$
--
--   then for every algorithm $p$ there is a model $M\in\mathcal M$ with
--
--   $$
--   \mathbb E_{M,p}[\mathrm{Reg}(T)]\ge C\cdot\mathrm{dec}^{\mathrm c}_{\varepsilon_T}(\mathcal M)\cdot T. \tag{6.31}
--   $$
--
--   Here $\mathrm{dec}^{\mathrm c}_{\varepsilon}(\mathcal M)=\sup_{\widehat M\in\mathrm{co}(\mathcal M)}\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M\cup\{\widehat M\},\widehat M)$ is the constrained Decision-Estimation Coefficient, and the regret is measured against the optimal decision of the true model $M$.
--
--   The constrained DEC is thus a lower bound on the minimax regret of every model class: no algorithm, however adaptive, can achieve regret below the order of $\mathrm{dec}^{\mathrm c}_{1/\sqrt T}(\mathcal M)\cdot T$ on every model of the class.
--
--   Differences from the source:
--   - reading: "$c>0$ a sufficiently small numerical constant" and "$\gtrsim$" → $\exists c_0>0,\ \exists C>0,\ \forall c\in(0,c_0]$, both constants chosen before the spaces, the class, $T$ and the algorithm; reason: the stronger of the readings of the two informal symbols, with constants that are absolute as in the source [43] ("universal constants")
--   - reading: reward space $\mathcal R\subseteq\mathbb R$ → rewards in $[0,1]$; reason: the proof states "since rewards are in $[0,1]$" (p. 109), and the cited source [43] assumes $\mathcal R=[0,1]$ throughout; without bounded rewards the mean rewards and the DEC need not exist
--   - encoding: decision space $\Pi$, observation space $\mathcal O$ → arbitrary measurable spaces in a fixed universe; reason: Lean convention; every measurable decision and observation space is an instance
--   - encoding: "for all $T$" with $\varepsilon_T=c/\sqrt T$ → $T\in\mathbb N$, $T\ge1$; reason: $\varepsilon_T$ is undefined at $T=0$
--   - generalization: $f^M(\pi_M)$ with $\pi_M=\arg\max_\pi f^M(\pi)$ → $\sup_\pi f^M(\pi)$; reason: equal whenever the argmax exists, which the notation presupposes
--   - reading: $\mathrm{co}(\mathcal M)$ → the set of finite mixtures $\sum_i\lambda_iM_i$; reason: the notes do not define it; this is the convex hull
--   - reading: $\mathbb E_{\pi\sim p}[D^2_{\mathrm H}(M(\pi),\widehat M(\pi))]$ → a Lebesgue integral in $[0,\infty]$ (the lower integral when $\pi\mapsto D^2_{\mathrm H}(M(\pi),\widehat M(\pi))$ is not measurable, possible only for an observation space that is not countably generated); reason: equal to the expectation whenever the integrand is measurable, which the notes presuppose; where it is not, the notes' expectation is undefined
--   - encoding: footnote 15 (value $0$ when some constraint set is empty) → the real supremum of the empty set is $0$; reason: for a class of models all feasible values are nonnegative, so the infimum is then $0$; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 28, (6.30)–(6.31), pp. 105–106; constrained DEC §6.5.1, p. 104; regret (6.3), p. 94

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_IsModel
import Definitions.Def_FoundationsRL_DECLower_constrainedDEC
import Definitions.Def_FoundationsRL_DECLower_expRegret

open MeasureTheory ProbabilityTheory

universe u

namespace FoundationsRL.DECLower

/-- **Proposition 28 (DEC Lower Bound).**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Proposition 28, (6.30)–(6.31), pp. 105–106: "Let ε_T := c · 1/√T, where c > 0 is a
sufficiently small numerical constant. For all T such that the condition dec^c_{ε_T}(M) ≥ 10 ε_T
(6.30) is satisfied, it holds that for any algorithm, there exists a model M ∈ M for which
E[Reg(T)] ≳ dec^c_{ε_T}(M) · T. (6.31)"

There are absolute constants `c₀ > 0` and `C > 0` such that for every `c ∈ (0, c₀]`, all
decision and observation spaces, every class `M` of models with rewards in `[0, 1]`, every
`T ≥ 1` with `dec^c_{c/√T}(M) ≥ 10 c/√T`, and every algorithm, some `M ∈ M` has
`E_M[Reg(T)] ≥ C · dec^c_{c/√T}(M) · T`.

**Formalization Note.** "`c` sufficiently small" and "`≳`" are read as `∃ c₀ C > 0, ∀ c ∈ (0, c₀]`,
with both constants chosen before the spaces, the class, `T` and the algorithm (the stronger
reading). `dec^c_ε(M)` is `constrainedDEC`: supremum over finite mixtures `M̂` of the class, with
`M̂` added to the class (not the notes' simplified version of p. 107). `T ≥ 1` because `ε_T` is
undefined at `T = 0`. Rewards in `[0, 1]` as in the proof (p. 109) and in the cited source
[43] (Foster, Golowich & Han, arXiv:2301.08215). The universe level `u` of the spaces is a
parameter of the statement. -/
theorem constrainedDEC_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ (D O : Type u) [MeasurableSpace D] [MeasurableSpace O]
        (Ms : Set (Kernel D (ℝ × O))),
        (∀ M ∈ Ms, IsModel M) →
        ∀ T : ℕ, 1 ≤ T →
        10 * (c / Real.sqrt T) ≤ constrainedDEC (c / Real.sqrt T) Ms →
        ∀ alg : Algorithm D O, ∃ M ∈ Ms,
          C * constrainedDEC (c / Real.sqrt T) Ms * T ≤ expRegret alg M T := by sorry

end FoundationsRL.DECLower
