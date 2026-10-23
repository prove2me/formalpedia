-- Prove2me | Theorems.Thm_InfoNudge_Cutoff_lemma_1
-- name    : InfoNudge.Cutoff.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:47.274806+00:00
-- url     : https://prove2.me/theorems/2a04194f-3974-4fe8-b8b3-f07d6788d3b7
-- title:
--   Lemma 1, p. 9 — the intrapersonal game has a unique efficient SPE: both selves consume iff the mean belief is below tᵃ
-- statement:
--   Let $\beta\in(0,1)$, $\delta\in(0,1]$ and $\beta\delta^2C>1$, and let $t^a=1/(\beta\delta^2C)$. Consider the intrapersonal game at mean posterior belief $\hat\theta\in\mathbb R$: the date-0 self chooses $x_0\in\{0,1\}$, the date-1 self observes $x_0$ and chooses $x_1\in\{0,1\}$, with payoffs $U_0(x_0,x_1,\hat\theta)$ and $U_1(x_0,x_1,\hat\theta)$ from (1)–(2).
--
--   Then:
--
--   1. the game has an efficient subgame-perfect equilibrium (no other subgame-perfect equilibrium gives both selves weakly more and one strictly more);
--   2. in every efficient subgame-perfect equilibrium, the date-0 self and the date-1 self (on the equilibrium path) both consume if $\hat\theta<t^a$ and both abstain if $\hat\theta\ge t^a$;
--   3. if $\hat\theta\ne t^a$, the subgame-perfect equilibrium is unique: both selves always consume when $\hat\theta<t^a$ and always abstain when $\hat\theta>t^a$.
--
--   $$x_0=x_1=1_{\{\hat\theta<t^a\}}.$$
--
--   This lemma is what makes the recommendations of a persuasion mechanism self-enforcing exactly when the posterior mean following "consume" is below $t^a$ and the one following "abstain" is at least $t^a$, i.e. it justifies the constraints (6)–(7).
--
--   **Formalization Note** Strategies are pure: at $\hat\theta=t^a$ the paper notes a continuum of mixed equilibria, which are not modelled; efficiency is Pareto efficiency among pure equilibria. At $\hat\theta=t^a$ the date-1 self's choice at the off-path node is unrestricted, so uniqueness there is stated for the equilibrium outcome.
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), p. 9, Lemma 1 (with the discussion on p. 10)

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

namespace InfoNudge.Cutoff

theorem lemma_1 (M : Params) (hS : Standing M) (θh : ℝ) :
    (∃ (a0 : Bool) (s1 : Bool → Bool), IsEfficientSPE M θh a0 s1) ∧
    (∀ (a0 : Bool) (s1 : Bool → Bool), IsEfficientSPE M θh a0 s1 →
      a0 = decide (θh < ta M) ∧ s1 a0 = decide (θh < ta M)) ∧
    (θh ≠ ta M → ∀ (a0 : Bool) (s1 : Bool → Bool), IsSPE M θh a0 s1 →
      a0 = decide (θh < ta M) ∧ s1 = fun _ => decide (θh < ta M)) := by sorry

end InfoNudge.Cutoff
