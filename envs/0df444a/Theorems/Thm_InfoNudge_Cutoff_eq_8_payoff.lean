-- Prove2me | Theorems.Thm_InfoNudge_Cutoff_eq_8_payoff
-- name    : InfoNudge.Cutoff.eq_8_payoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:48.285289+00:00
-- url     : https://prove2.me/theorems/b4cdbd32-5e71-4795-afb3-b0b42aa3dd55
-- title:
--   (8), p. 13 — the date-0 expected payoff of a mechanism is (1 + δ)/tᵃ times tʰE[π(θ)] − E[θπ(θ)]
-- statement:
--   Under the standing assumptions of the model, let $\pi$ be a persuasion mechanism, a measurable map from types to $[0,1]$. If the decision maker consumes at both dates when consumption is recommended and abstains at both dates otherwise, his expected date-0 utility is
--   $$E\big[\pi(\theta)\,U_0(1,1,\theta)+(1-\pi(\theta))\,U_0(0,0,\theta)\big]=\frac{1+\delta}{t^a}\Big(t^hE[\pi(\theta)]-E[\theta\pi(\theta)]\Big).$$
--
--   Hence, up to the positive constant $(1+\delta)/t^a$, the optimal-design problem is to maximize $t^hE[\pi(\theta)]-E[\theta\pi(\theta)]$ over incentive-compatible mechanisms, which is problem (8).
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), p. 13, eq. (8)

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

namespace InfoNudge.Cutoff

theorem eq_8_payoff (M : Params) (hS : Standing M) (π : ℝ → ℝ) (hπ : IsMechanism π) :
    (∫ θ, (π θ * U0 M 1 1 θ + (1 - π θ) * U0 M 0 0 θ) ∂M.P) =
      (1 + M.δ) / ta M * objective M π := by sorry

end InfoNudge.Cutoff
