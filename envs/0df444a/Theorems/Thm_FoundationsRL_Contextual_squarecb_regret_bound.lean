-- Prove2me | Theorems.Thm_FoundationsRL_Contextual_squarecb_regret_bound
-- name    : FoundationsRL.Contextual.squarecb_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:00:41.205917+00:00
-- url     : https://prove2.me/theorems/521a4d3c-2700-47e1-b5a3-64cfb458cf15
-- title:
--   Proposition 10 — SquareCB regret bound
-- statement:
--   This is **Proposition 10** (Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making*, p. 51), the regret bound for the **SquareCB** algorithm — the
--   main result of this mission.
--
--   Consider the contextual bandit protocol over $T$ rounds with context sequence
--   $x_1,\dots,x_T$ (arbitrary, possibly adversarial), action set $\Pi=\{1,\dots,A\}$, and
--   ground-truth reward function $f^\star \in F$. Suppose the decision-maker has access to an
--   online regression oracle (Definition 3) with estimation-error guarantee
--   $\mathrm{EstSq}(F,T,\delta)$: at each round $t$ it produces $\hat f_t$ from the history so
--   far, with $\sum_{t=1}^T \mathbb{E}_{\pi_t\sim p_t}[(\hat f_t(x_t,\pi_t)-f^\star(x_t,\pi_t))^2]
--   \le \mathrm{EstSq}(F,T,\delta)$ with probability at least $1-\delta$. SquareCB samples
--   $\pi_t \sim p_t = \mathrm{IGW}_\gamma(\hat f_t(x_t,\cdot))$ (Definition 4) at every round,
--   with exploration parameter
--
--   $$
--   \gamma = \sqrt{\frac{TA}{\mathrm{EstSq}(F,T,\delta)}}.
--   $$
--
--   Then, on the event that the oracle's guarantee holds, SquareCB's regret satisfies
--
--   $$
--   \mathrm{Reg} \le 2\sqrt{A \, T \, \mathrm{EstSq}(F,T,\delta)}.
--   $$
--
--   As a special case, when $F$ is finite and the averaged exponential weights algorithm is used
--   as the oracle, $\mathrm{EstSq}(F,T,\delta) \lesssim \log(|F|/\delta)$, giving
--   $\mathrm{Reg} \lesssim \sqrt{AT\log(|F|/\delta)}$: a regret bound with no dependence on the
--   size of the context space, matching the optimal $\sqrt{T}$-rate (unlike the $T^{2/3}$-rate of
--   $\varepsilon$-Greedy, Proposition 8) and depending on the model class only through
--   $\log|F|$.
--
--   The proof is a near-immediate consequence of the Inverse Gap Weighting inequality
--   (Proposition 9): applying it at every round with $\hat f_t(x_t,\cdot)$ and $f^\star(x_t,\cdot)$
--   and summing gives $\mathrm{Reg} \le TA/\gamma + \gamma \cdot \mathrm{EstSq}(F,T,\delta)$, and
--   the stated $\gamma$ exactly balances the two terms.
--
--   **Formalization Note** The book states the conclusion as $\mathrm{Reg}\lesssim
--   \sqrt{AT\cdot\mathrm{EstSq}(F,T,\delta)}$; the constant $2$ here is the exact constant the
--   proof establishes at the stated optimal $\gamma$ (no hidden slack). The model class $F$ and
--   the fact $f^\star \in F$ enter only through the abstract bound $\mathrm{EstSq}$, since neither
--   the algorithm nor this proposition's proof otherwise references $F$. The probability-$(1-\delta)$
--   qualifier of the source is the hypothesis `OracleGuarantee ... EstSq` (see that definition's
--   Formalization Note); the conclusion is then a deterministic consequence of that event holding.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 51, Proposition 10

import Mathlib
import Definitions.Def_FoundationsRL_Contextual_IsIGW
import Definitions.Def_FoundationsRL_Contextual_OracleGuarantee
import Definitions.Def_FoundationsRL_Contextual_regret

namespace FoundationsRL.Contextual

/-- Proposition 10 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, p. 51): SquareCB's regret bound. Given a context
sequence `x : Fin T → X`, ground-truth reward function `fstar` with optimal policy `pistar`,
an online regression oracle producing estimates `fhat` with cumulative squared-error
guarantee `EstSq` (`OracleGuarantee`), and SquareCB's realized action distributions
`p t = IGW_γ(fhat t (x t))` with `γ = √(TA / EstSq)`, the regret is at most
`2√(A T EstSq)` (the book's `≲ √(AT · EstSq(F,T,δ))`, with the exact constant `2` that the
proof establishes by balancing `TA/γ` against `γ · EstSq`). -/
theorem squarecb_regret_bound {X : Type*} {A T : ℕ} (hT : 0 < T)
    (x : Fin T → X) (fstar : X → Fin A → ℝ) (pistar : X → Fin A)
    (hpistar : ∀ (x' : X) (π : Fin A), fstar x' π ≤ fstar x' (pistar x'))
    (fhat : Fin T → X → Fin A → ℝ) (bstar : Fin T → Fin A)
    (EstSq : ℝ) (hEstSq : 0 < EstSq)
    (γ : ℝ) (hγ : γ = Real.sqrt ((T : ℝ) * A / EstSq))
    (p : Fin T → Fin A → ℝ) (hp : ∀ t, IsIGW A (fhat t (x t)) γ (bstar t) (p t))
    (hOracle : OracleGuarantee A T x fhat fstar p EstSq) :
    regret A T x fstar pistar p ≤ 2 * Real.sqrt ((A : ℝ) * T * EstSq) := by sorry

end FoundationsRL.Contextual
