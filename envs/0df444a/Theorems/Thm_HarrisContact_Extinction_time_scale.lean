-- Prove2me | Theorems.Thm_HarrisContact_Extinction_time_scale
-- name    : HarrisContact.Extinction.time_scale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:51:40.397025+00:00
-- url     : https://prove2.me/theorems/ab4de79c-50c2-46f7-b15c-6b66c1d9e51a
-- title:
--   §7, proof of Theorem 7.1, p. 981 — a change of time scale: P_t for rates (cμ, cλ) equals P_{ct} for (μ, λ)
-- statement:
--   Let $\mu$ and $\lambda_0,\lambda_1,\dots$ be rates and $c>0$. Multiplying every rate by $c$ runs the chain $c$ times faster: for all times $t$ and finite $\xi,\eta\subset Z_d$,
--   $$P^{(c\mu,\,c\lambda)}_t(\xi,\eta)=P^{(\mu,\,\lambda)}_{ct}(\xi,\eta),$$
--   and consequently
--   $$p^{(c\mu,\,c\lambda)}_\infty(\xi)=p^{(\mu,\,\lambda)}_\infty(\xi).$$
--
--   This is the "change of time scale" with which the proof of Theorem 7.1 reduces to the normalized case $\mu=1$.
--
--   **Formalization Note** No sign hypotheses on the rates are needed for the identity of the minimal transition functions, so none are assumed.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.1, p. 981 ("a change of time scale")

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- §7, proof of Theorem 7.1 (p. 981), "a change of time scale": multiplying all rates by c > 0
runs the process c times faster, so p_∞ is unchanged. -/
theorem time_scale {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (c : ℝ) (hc : 0 < c) :
    (∀ (t : ℝ) (ξ η : Config d),
        trans (c * μ) (fun k => c * lam k) t ξ η = trans μ lam (c * t) ξ η) ∧
      ∀ ξ : Config d, survInf (c * μ) (fun k => c * lam k) ξ = survInf μ lam ξ := by sorry

end HarrisContact.Extinction
