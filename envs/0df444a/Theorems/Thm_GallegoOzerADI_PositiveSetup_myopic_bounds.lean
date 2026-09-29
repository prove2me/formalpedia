-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_myopic_bounds
-- name    : GallegoOzerADI.PositiveSetup.myopic_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:52:10.207236+00:00
-- url     : https://prove2.me/theorems/a4fd474a-e682-4606-9323-e89fbb4e335b
-- title:
--   Lemma 3 — $S^m \le S_t(o_t) \le \overline{S}$ and $s^m \le s_t(o_t)$
-- statement:
--   Consider a stationary instance of the finite-horizon inventory model with advance demand information and set-up costs (Definition `Model`): $G_t = G$, $K_t = K$, $\alpha_t = \alpha$ and the demand law $\mu_t = \nu$ for every period, with $N > L + 1$. Let $S^m$, $s^m$ and $\overline{S}$ be the myopic levels of $G$ (Definition `MyopicLevels`). Fix a period $1 \le t \le T$ and a vector $o_t$ of observed demands with nonnegative components, and let $S_t(o_t)$ be the least minimizer of $V_t(\cdot, o_t)$ and $s_t(o_t) = \max\{x : H_t(x, o_t) \le 0\}$. Then
--
--   $$
--   S^m \le S_t(o_t) \le \overline{S} \qquad\text{and}\qquad s^m \le s_t(o_t).
--   $$
--
--   The optimal order-up-to level with advance demand information is bracketed by quantities computed from the single-period cost alone, and the optimal reorder point is never below the myopic one. These bounds are similar to those of Veinott (1966) and Iglehart (1963) for the classical model, and they are the inputs of the horizon result, Theorem 2.
--
--   **Formalization Note** The statement takes $S_t(o_t)$ and $s_t(o_t)$ as given by their characterizations (least minimizer, greatest element of $\{H_t \le 0\}$), so it does not presuppose Theorem 1, which asserts their existence. The observed demands $o_t$ are restricted to be nonnegative: they are cumulative observed demands (Eq. (1)) and every reachable state has this property. For a negative first component the lower bound $S^m \le S_t(o_t)$ can fail (e.g. $G(y) = y^2$ on $[-200, 200]$ extended linearly outside, $K = 1$, $\alpha = 1/2$, zero demand, $T = 2$, $t = 1$, $o_{t,t+L+1} = -100$ gives $S_1(o_1) = -100/3 < 0 = S^m$), so the paper's "any fixed vector $o_t$" is read over the state space.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Lemma 3 (proof p. 1358)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

theorem myopic_bounds {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ) (K α : ℝ)
    (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G) (hK : ∀ t, P.K t = K)
    (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t) (htT : t ≤ P.T)
    (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j) (S s : ℝ)
    (hS : IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} S)
    (hs : IsGreatest {x | P.H t x o ≤ 0} s) :
    myopicOrderUpTo G ≤ S ∧ S ≤ myopicUpperLevel G K α ∧ myopicReorderPoint G K ≤ s := by sorry

end GallegoOzerADI.PositiveSetup
