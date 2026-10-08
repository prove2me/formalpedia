-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_myopic_order_up_to_optimal
-- name    : GallegoOzerADI.PositiveSetup.myopic_order_up_to_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:52:34.581923+00:00
-- url     : https://prove2.me/theorems/b8c3e401-66b7-46da-9c67-633cc2cffbfd
-- title:
--   Theorem 2 — if $o_{t,t+L+1} \ge \overline{S} - s^m$ then $S_t(o_t) = S^m$
-- statement:
--   Consider a stationary instance of the finite-horizon inventory model with advance demand information and set-up costs (Definition `Model`): the single-period cost $G_t = G$, the set-up cost $K_t = K$, the discount factor $\alpha_t = \alpha$ and the demand law $\mu_t = \nu$ do not depend on $t$, and $N > L + 1$. Let $S^m$ be the least minimizer of $G$, $s^m = \max\{y \le S^m : G(y) \ge K + G(S^m)\}$ and $\overline{S} = \inf\{y > S^m : G(y) > G(S^m) + \alpha K\}$ (Definition `MyopicLevels`). Fix a period $1 \le t \le T$ and a vector $o_t = (o_{t,t+L+1}, \dots, o_{t,t+N-1})$ of observed demands with nonnegative components. If
--
--   $$
--   o_{t,t+L+1} \ge \overline{S} - s^m,
--   $$
--
--   then the optimal order-up-to level equals the myopic one:
--
--   $$
--   S_t(o_t) = \min\{y : V_t(y, o_t) \le V_t(x, o_t) \text{ for all } x\} = S^m.
--   $$
--
--   Once the demand already observed for period $t + L + 1$, the first period beyond the protection period, is large enough, the advance demand information for later periods can be ignored when choosing the order-up-to level. The threshold $\overline{S} - s^m$ depends only on the single-period cost, the set-up cost and the discount factor.
--
--   **Formalization Note** The conclusion is `IsLeast {y | ∀ x, V_t(y, o_t) ≤ V_t(x, o_t)} S^m`: $S^m$ is a global minimizer of $V_t(\cdot, o_t)$ and no smaller level is. Only the first component $o_{t,t+L+1}$ is compared with the threshold. The other components are required to be nonnegative, as all reachable observed-demand vectors are (Eq. (1) with nonnegative demands). The paper's proof uses the lower bound $s^m \le s_{t+1}(o_{t+1})$ of Lemma 3, which needs this, and a negative component of $o_t$ would become a negative first component at a later period. The terminal case $t = T$ is included: there $V_T = G$ and the statement says that $S^m$ is the least minimizer of $G$.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1350, Theorem 2 (proof p. 1357)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

theorem myopic_order_up_to_optimal {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ)
    (K α : ℝ) (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G)
    (hK : ∀ t, P.K t = K) (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0) :
    IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} (myopicOrderUpTo G) := by sorry

end GallegoOzerADI.PositiveSetup
