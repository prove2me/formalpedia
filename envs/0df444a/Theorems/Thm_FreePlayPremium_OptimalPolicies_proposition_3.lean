-- Prove2me | Theorems.Thm_FreePlayPremium_OptimalPolicies_proposition_3
-- name    : FreePlayPremium.OptimalPolicies.proposition_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:28:54.794134+00:00
-- url     : https://prove2.me/theorems/699177dd-f398-4ea8-89d7-a1875f93b070
-- title:
--   Proposition 3 — optimal advertising and premium subscription pricing
-- statement:
--   Consider the full continuous-time Problem (3): $0<\alpha_d,\alpha_u<v$, $\alpha_d\ne\alpha_u$, any finite $T>0$, $r\ge0$, and any twice differentiable advertising cost on $[0,\infty)$ with $C'>0,C''>0$. Controls $a,p$ are nonnegative and measurable, population stays in $[0,1]$, starts at zero and follows the nonsingular expanded dynamics. Profit compares all admissible policies, including those with infinite expenditure assigned profit $-\infty$.
--   There exists an attained globally optimal policy representative $(a^*,p^*,n^*)$ such that advertising is strictly decreasing on $[0,T]$, has its right limit at zero equal to $a^*(0)$, and satisfies
--   $$a^*(T)=\lim_{t\uparrow T}a^*(t)=0.$$
--   There is $\tau\in[0,T)$ such that $S(p^*(t))p^*(t)=0$ for $0\le t<\tau$, and $S(p^*(t))p^*(t)>0$ for $\tau<t\le T$.
--   If $\alpha_d>\alpha_u$, price is strictly decreasing on $[\tau,T]$ and
--   $$p^*(\tau)=\lim_{t\downarrow\tau}p^*(t)=\alpha_d,\qquad p^*(T)=\lim_{t\uparrow T}p^*(t)=\max(\alpha_d/2,\alpha_u).$$
--   If $\alpha_d<\alpha_u$, $p^*(t)=\alpha_d$ for every $t\in[\tau,T]$. At the threshold the downward-dominant response has zero premium share, whereas the upward-dominant response has a positive paid price. No uniqueness is claimed.
--   The result retains both regimes and every endpoint. It makes no co-state assumption, no discount-rate restriction, and no restriction of competitors to a prescribed price range or policy shape. Source findings I2–I5 are retained separately without repairing this target.
--
--   Differences from the source:
--   - encoding: continuous-time controls and differential state equation on [0,T] → Lebesgue-measurable nonnegative control representatives and an integrable-drift integral equation with state in [0,1]; reason: this is the standard absolutely continuous trajectory convention and permits the printed switching policy
--   - reading: the state equation contains 1/n although n(0)=0 → the nonsingular expanded drift (a+B(p)n-1)(1-n) also governs zero population; reason: Eq. (5) supplies this extension; using total real division at zero would give a different drift
--   - encoding: discounted revenue minus advertising expenditure → extended-real profit with a nonnegative integral of C(a)-C(0) and finite baseline C(0); reason: this agrees at finite profit and assigns minus infinity to infinite expenditure without a zero-valued Bochner default
--   - encoding: positive first and second advertising-cost derivatives on nonnegative strengths → derivatives within the nonnegative half-line, including right derivatives at zero; reason: only the feasible cost domain is relevant and no smooth extension to negative strengths is required
--   - reading: optimal policies decrease and reach the stated endpoint values → an attained globally optimal representative with strict advertising decrease, strict post-introduction price decrease in the downward-dominant regime, and matching one-sided endpoint limits; reason: the brief requires the stronger advertising reading, p. 15 explicitly requires strict price decrease, and endpoint limits exclude changes at isolated times as a substitute for the claimed paths
--   - encoding: premium subscription is introduced after a threshold that can be zero → there is a threshold in [0,T) with zero per-player payment before it and positive payment afterwards; reason: payment S(p)p includes the Appendix p. 34 equivalence between a zero-price premium offer and no paid subscription
-- source:
--   Mai and Hu (2022), Optimizing Free-to-Play Multiplayer Games with Premium Subscription, Management Science, https://doi.org/10.1287/mnsc.2022.4510, Proposition 3, printed p. 14 (PDF p. 14), strictness on printed p. 15 (PDF p. 15); setup printed pp. 6–14 and proof printed pp. 34–37

import Definitions.Def_FreePlayPremium_OptimalPolicies_Problem

open Set Filter
open scoped Topology

namespace FreePlayPremium.OptimalPolicies

theorem proposition_3 (M : Problem) (hM : M.Valid) :
    ∃ q : ControlPath, M.GloballyOptimal q ∧
      StrictAntiOn q.advertising (Icc 0 M.horizon) ∧
      q.advertising M.horizon = 0 ∧
      Tendsto q.advertising (𝓝[>] 0) (𝓝 (q.advertising 0)) ∧
      Tendsto q.advertising (𝓝[<] M.horizon) (𝓝 0) ∧
      ∃ τ : ℝ, 0 ≤ τ ∧ τ < M.horizon ∧
        (∀ t ∈ Ico 0 τ, payment M.players (q.price t) = 0) ∧
        (∀ t ∈ Ioc τ M.horizon, 0 < payment M.players (q.price t)) ∧
        (M.players.up < M.players.down →
          q.price τ = M.players.down ∧
          Tendsto q.price (𝓝[>] τ) (𝓝 M.players.down) ∧
          StrictAntiOn q.price (Icc τ M.horizon) ∧
          q.price M.horizon = max (M.players.down / 2) M.players.up ∧
          Tendsto q.price (𝓝[<] M.horizon)
            (𝓝 (max (M.players.down / 2) M.players.up))) ∧
        (M.players.down < M.players.up →
          ∀ t ∈ Icc τ M.horizon, q.price t = M.players.down) := by sorry

end FreePlayPremium.OptimalPolicies
