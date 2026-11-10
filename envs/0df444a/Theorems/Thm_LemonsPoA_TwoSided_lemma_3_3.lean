-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_lemma_3_3
-- name    : LemonsPoA.TwoSided.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:26.342985+00:00
-- url     : https://prove2.me/theorems/44706f0b-5284-4a11-a52e-4c4204fca27e
-- title:
--   Lemma 3.3 — fine-menu limit: $u_{Q_n}(k)\to u(k)$ and $E[u_{Q_n}(\hat v_S)]\to E[u(\hat v_S)]$
-- statement:
--   Let $\hat v_B$ be an integrable buyer value with law $\nu_B$, and let $u_Q$ and $u$ be the finite-menu and continuous monopoly profits against $\hat v_B$ ((30), (32)): $u_Q(k)=\max(\{0\}\cup\{(q-k)\Pr[\hat v_B>q]:q\in Q,q>k\})$ and $u(k)=\sup_{q>k}(q-k)\Pr[\hat v_B>q]$. Let $(Q_n)$ be a fine sequence of finite menus. Then
--   $$\lim_{n\to\infty}u_{Q_n}(k)=u(k)\quad\text{for every }k\in\mathbb R,$$
--   and for every integrable seller value $\hat v_S$ (law $\nu_S$),
--   $$\lim_{n\to\infty}E[u_{Q_n}(\hat v_S)]=E[u(\hat v_S)].$$
--
--   The lemma lets the reduction pass from equilibria on finite menus to the continuous screening problem.
--
--   **Formalization Note** The values enter through their laws: $E[u_{Q_n}(\hat v_S)]=\int u_{Q_n}\,d\nu_S$.
--
--   Differences from the source:
--   - encoding: random variables $\hat v_B$, $\hat v_S$ → their laws $\nu_B$, $\nu_S$ (probability measures on $\mathbb R$); reason: $u_Q$, $u$ and $E[u(\hat v_S)]$ depend on the random variables only through their laws
--   - encoding: fine: $\sup_{|q|\le H}\mathrm{dist}(q,Q_n)\to 0$ for every $H>0$ (24) → `IsFine`: for every $H>0$, $\varepsilon>0$, eventually every $|q|\le H$ has a menu price within $\varepsilon$; reason: equivalent: $\mathrm{dist}(\cdot,Q_n)$ is continuous, the minimum over a finite menu is attained, and an empty menu has distance $+\infty$ and fails both
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 19, Lemma 3.3

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Monopoly

open MeasureTheory Filter Topology

namespace LemonsPoA.TwoSided

/-- Lemma 3.3 (p. 19): along a fine menu sequence, finite-menu monopoly profit converges to the
continuous monopoly profit, pointwise and in expectation over an integrable seller value. -/
theorem lemma_3_3 (νB : Measure ℝ) [IsProbabilityMeasure νB] (hνB : Integrable id νB)
    (Qs : ℕ → Finset ℝ) (hQs : IsFine Qs) :
    (∀ k : ℝ, Tendsto (fun n => uQ νB (Qs n) k) atTop (𝓝 (u νB k))) ∧
      ∀ νS : Measure ℝ, IsProbabilityMeasure νS → Integrable id νS →
        Tendsto (fun n => ∫ k, uQ νB (Qs n) k ∂νS) atTop (𝓝 (∫ k, u νB k ∂νS)) := by sorry

end LemonsPoA.TwoSided
