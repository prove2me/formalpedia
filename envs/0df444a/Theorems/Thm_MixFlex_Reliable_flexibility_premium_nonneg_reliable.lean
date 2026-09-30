-- Prove2me | Theorems.Thm_MixFlex_Reliable_flexibility_premium_nonneg_reliable
-- name    : MixFlex.Reliable.flexibility_premium_nonneg_reliable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:03:32.466791+00:00
-- url     : https://prove2.me/theorems/8e53509b-69c2-4e89-bfa6-6aa97d4eded9
-- title:
--   Proposition 4 — with perfectly reliable resources, $\Delta\ge 0$ for every nondecreasing utility, the loss-averse and the CVaR objective
-- statement:
--   Consider $N$ products with common margin $p>0$, served either by $N$ dedicated resources of marginal cost $c>0$ (network SD) or by one flexible resource of marginal cost $c_{N+1}$ (network SF), all perfectly reliable. The firm has initial wealth $w_0$, and the demand vector $\tilde X$ is nonnegative with an arbitrary joint distribution. Let $\beta\ge 1$ and $\eta\in(0,1]$. Then for every flexible cost $c_{N+1}\le c$:
--   1. for every nondecreasing utility $u$ (the class $U_1$), every nonnegative SD investment $K$ is matched by a nonnegative SF investment $K_{N+1}$ with
--   $$
--   E\big[u(w^{SD}(K))\big]\le E\big[u(w^{SF}(K_{N+1}))\big];
--   $$
--   2. the same holds for the loss-averse objective (6);
--   3. for the CVaR objective (8), every pair $(K,v)$ with $K\ge0$ is matched by a pair $(K_{N+1},v')$ with $K_{N+1}\ge 0$ and a CVaR bracket at least as large.
--
--   In the paper's terms: the flexibility premium satisfies $\Delta\ge 0$ for all $u_1\in U_1$, and in particular for the loss-averse and the CVaR objective functions. Together with Proposition 1 (risk neutrality), this identifies when the intuition "flexibility is worth paying for" is valid: whenever supply is perfectly reliable, whatever the demand distribution and whatever the (monotone) risk attitude.
--
--   **Formalization Note** The flexibility premium $\Delta=(c^I_{N+1}-c)/c$ of Definitions 1–2 is not defined as a number (the indifference cost need not be unique); "$\Delta\ge 0$" is encoded as "SF is weakly preferred for every $c_{N+1}\le c$", which is how p. 41 reads $\Delta$. "Weakly preferred" ($V^{SF,*}\ge V^{SD,*}$) is encoded without suprema, as the matching statements above. Perfect reliability ($\theta=1$) is built into the terminal wealths, which then no longer involve $\lambda$. Nonnegative, measurable demand and $p,c>0$ are stated explicitly; no density, independence or integrability of demand is assumed ("Let $\tilde X$ have any joint distribution").
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 45, §3.3, PROPOSITION 4; p. 41, DEFINITIONS 1–2

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model

open MeasureTheory

namespace MixFlex.Reliable
theorem flexibility_premium_nonneg_reliable (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X) :
    (∀ u : ℝ → ℝ, Monotone u → PremiumNonneg P (SFPreferredEU P μ X u)) ∧
      PremiumNonneg P (SFPreferredLA P μ X) ∧
      PremiumNonneg P (SFPreferredCVaR P μ X) := by sorry
end MixFlex.Reliable
