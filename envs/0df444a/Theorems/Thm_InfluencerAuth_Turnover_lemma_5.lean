-- Prove2me | Theorems.Thm_InfluencerAuth_Turnover_lemma_5
-- name    : InfluencerAuth.Turnover.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:59.491556+00:00
-- url     : https://prove2.me/theorems/a110728e-e89f-4fe8-84c5-31e31b82b0d2
-- title:
--   Lemma 5, p. 9 — value of always being authentic under turnover: V̄(A_t) = ∫ e^{−r(u−t)}/[β/(β−x) + ((1−A_tβ/(β−x))/A_t)e^{−(β−x)(u−t)}] du
-- statement:
--   Let $\beta > 0$, $r > 0$ and a turnover rate $x$ with $0 < x < \beta$. Let $0 < A_0 < 1$, and let $A$ be an admissible awareness path from $A_0$ under the policy of always being authentic, i.e. a solution of $\frac{dA_t}{dt} = \beta A_t(1 - A_t) - x A_t$ with $A(0) = A_0$ (in integral form). Then the discounted profit of always being authentic is
--   $$
--   \int_0^\infty e^{-r t} A_t\,dt \;=\; \overline V(A_0) \;=\; \int_0^\infty \frac{e^{-r s}}{\dfrac{\beta}{\beta - x} + \dfrac{1 - A_0\frac{\beta}{\beta - x}}{A_0}\, e^{-(\beta - x) s}}\,ds .
--   $$
--
--   This is the closed form of the always-authentic value function with turnover: the integrand is $e^{-rs}$ times the logistic awareness path with carrying capacity $(\beta - x)/\beta$. It is the value against which Proposition 3 compares every deviation.
--
--   **Formalization Note** The paper writes the value from a general time $t$ with current awareness $A_t$; by time invariance this is stated at $t = 0$ with $s = u - t$. The parameters $\gamma, \varphi$ of the model enter the definitions but play no role for the always-authentic policy, so the standing assumptions $0 < \gamma < 1$, $\varphi > 1$, $\gamma\varphi > 1$ are dropped; the statement is therefore slightly stronger than with them, and still true.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), Lemma 5, p. 9

import Mathlib
import Definitions.Def_InfluencerAuth_Turnover_Model

namespace InfluencerAuth.Turnover

theorem lemma_5 (γ φ β r x : ℝ) (hβ : 0 < β) (hr : 0 < r) (hx : 0 < x) (hxβ : x < β)
    (A₀ : ℝ) (hA₀ : A₀ ∈ Set.Ioo (0 : ℝ) 1) (A : ℝ → ℝ) (hA : IsPath β γ x A₀ ∅ A) :
    InfluencerAuth.Switch.discountedProfit γ φ r ∅ A = authValue β x r A₀ := by sorry

end InfluencerAuth.Turnover
