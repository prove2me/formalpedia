-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_change_of_measure
-- name    : FragileBandit.CauchyTail.change_of_measure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:46.383411+00:00
-- url     : https://prove2.me/theorems/d27346dc-a291-4154-a1bb-cad1c9841cef
-- title:
--   (80), Appendix D, p. 46 — change of measure on bandit histories, for any finite set of changed arms
-- statement:
--   **Change of measure on adaptive bandit histories.** Let $\pi$ be any bandit algorithm and let $\nu = (Q_1,\dots,Q_K)$ and $\tilde\nu = (\tilde Q_1,\dots,\tilde Q_K)$ be two environments that agree outside a finite set $S$ of arms: $Q_j = \tilde Q_j$ for $j \notin S$. For distributions $Q, \tilde Q$ write $dQ/d\tilde Q$ for the Radon–Nikodym derivative of the absolutely continuous part of $Q$ with respect to $\tilde Q$ (Lebesgue decomposition). For every horizon $T$ and every measurable event $E$ of the first $T$ rounds,
--
--   $$\mathbb P_{\nu\pi}(E) \;\ge\; \mathbb E_{\tilde\nu\pi}\Big[\mathbb I(E)\prod_{t \le T:\ A(t) \in S} \frac{dQ_{A(t)}}{d\tilde Q_{A(t)}}\big(Y(t)\big)\Big],$$
--
--   where $A(t)$ and $Y(t)$ are the arm and the reward of round $t$. The product equals $\prod_{j\in S}\prod_{s=1}^{N_j(T)} \frac{dQ_j}{d\tilde Q_j}(X_j(s))$. If moreover $Q_j \ll \tilde Q_j$ for every $j \in S$, equality holds.
--
--   This is the likelihood-ratio identity behind every lower bound of the paper: (13) and (43) change one arm, the case $i \ge 3$ of Theorem 1 (p. 39) changes $i-1$ arms, and (80) changes one arm without absolute continuity.
--
--   Differences from the source:
--   - generalization: one changed arm (arm 1), and the specific events C_n (80) / {N_2(T) > (1−γ)T} (43) → any finite set S of changed arms and any measurable event E of the first T rounds; equality clause under Q_j ≪ Q̃_j for j ∈ S; reason: S = {1} and E = C_n give (80); with absolute continuity the equality clause is (43); S = {1, …, i−1} is the change of measure of p. 39
--   - encoding: dQ/dQ̃, the density of the absolutely continuous part of Q with respect to Q̃ (Appendix D, p. 45); ∏_{t ≤ N_1(T)} dP_1/dP̃_1(X_1(t)) → Measure.rnDeriv (ν.P a) (ν'.P a) evaluated at the reward of every round t ≤ T whose arm a lies in S, in ℝ≥0∞; lower Lebesgue integral over E against banditMeasure ν' π T; reason: Mathlib's rnDeriv is the paper's convention; the product over rounds with arm in S is the product over the plays of the arms of S
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 46, Appendix D, (80); also p. 38, (43), and p. 13, (13)

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Change of measure on bandit histories (Appendix D, (80), p. 46; also (43), p. 38 and (13), p. 13),
for a finite set `S` of arms whose laws change from `ν̃` (here `ν'`) to `ν`. For every horizon `T` and
measurable event `E` of the first `T` rounds,
`P_νπ(E) ≥ E_ν̃π[𝟙_E ∏_{t ≤ T, A(t) ∈ S} (dQ_{A(t)}/dQ̃_{A(t)})(Y(t))]`, where `dQ/dQ̃` is the
Radon–Nikodym derivative of the absolutely continuous part of `Q` with respect to `Q̃`; equality holds when
`Q_j ≪ Q̃_j` for every `j ∈ S`. -/
theorem change_of_measure {K : ℕ} (π : BanditPolicy K) (ν ν' : StochasticBandit K)
    (S : Finset (Fin K)) (hS : ∀ j, j ∉ S → ν.P j = ν'.P j) (T : ℕ)
    (E : Set (BanditHistory K T)) (hE : MeasurableSet E) :
    (∫⁻ h in E, ∏ t : Fin T,
        (if (h t).1 ∈ S then (ν.P (h t).1).rnDeriv (ν'.P (h t).1) (h t).2 else 1)
        ∂(banditMeasure ν' π T)) ≤ banditMeasure ν π T E ∧
    ((∀ j ∈ S, ν.P j ≪ ν'.P j) →
      banditMeasure ν π T E =
        ∫⁻ h in E, ∏ t : Fin T,
          (if (h t).1 ∈ S then (ν.P (h t).1).rnDeriv (ν'.P (h t).1) (h t).2 else 1)
          ∂(banditMeasure ν' π T)) := by sorry

end FragileBandit.CauchyTail
