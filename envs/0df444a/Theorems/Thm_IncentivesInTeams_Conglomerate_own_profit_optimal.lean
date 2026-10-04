-- Prove2me | Theorems.Thm_IncentivesInTeams_Conglomerate_own_profit_optimal
-- name    : IncentivesInTeams.Conglomerate.own_profit_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:25:17.042985+00:00
-- url     : https://prove2.me/theorems/54d9b228-21c0-4350-8646-234ff0f9023a
-- title:
--   THEOREM 1 (Groves 1973): $W^{II}$ is an optimal incentive structure in the class $\mathscr{J}$
-- statement:
--   Consider a conglomerate organization (Conditions S.1–S.5) with finitely many subunits, finite component state spaces carrying probability weights, independent components (product law), arbitrary strategy sets $B_0$, $B_i$, and payoff components $v_0$, $v_i$. Let $\beta^*$ be a joint strategy satisfying Assumption A, and let $A_i$ be arbitrary constants. Let $W^{II}$ be the incentive structure (3.5),
--   $$\omega_i^{II}(\beta, s) = v_i[\delta_i(y_i(s)), \delta_0(y_0(s)); s_i] + C_i^{II}(y_0(s)),$$
--   with $C_i^{II}$ the head's conditional expectation, under $\beta^*$ and given his information $y_0$, of all payoff components other than subunit $i$'s, minus $A_i$ (3.3). Then $W^{II}$ belongs to the class $\mathscr{J}$ of (3.2), and it is optimal: for every subunit $i$ and every $\beta_i \in B_i$,
--   $$\bar\omega_i^{II}(\beta^*/\beta_i) \le \bar\omega_i^{II}(\beta^*),$$
--   with strict inequality whenever $\beta_i$ is not equivalent to $\beta_i^*$.
--
--   In words: rewarding each subunit with its own profit plus the head's expectation of everybody else's profit makes truthful reporting and the team-optimal decision rule the unique best reply of each subunit manager, using only information the head already has.
--
--   **Formalization Note.** Finite component state spaces, the one-exchange message protocol of §4.A, fixed message and observation codomains, and the factorized form of the conditional expectation in (3.3) are the conventions of the model file. The factorized form agrees with the literal (3.3) wherever the latter is defined; the literal quotient, which is $0$ on null conditioning events, would make the theorem false as soon as a subunit can send a message $\gamma_i^*$ never sends. Equivalence of strategies is the paper's footnote 5, over all $\beta \in B$.
-- source:
--   Groves, Incentives in Teams, Econometrica 41(4), 1973, p. 625, §3.B, THEOREM 1 (proof: Appendix, pp. 629–630)

import Mathlib
import Definitions.Def_IncentivesInTeams_Conglomerate_Model

namespace IncentivesInTeams.Conglomerate

theorem own_profit_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀] {S : ι → Type*}
    [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}
    (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (hA : T.AssumptionA βs) (A : ι → ℝ) :
    T.InClassJ (T.WII βs A) ∧ T.IsOptimal (T.WII βs A) βs := by sorry

end IncentivesInTeams.Conglomerate
