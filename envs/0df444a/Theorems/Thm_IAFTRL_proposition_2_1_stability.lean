-- Prove2me | Theorems.Thm_IAFTRL_proposition_2_1_stability
-- name    : IAFTRL.proposition_2_1_stability
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T09:30:53.630906+00:00
-- url     : https://prove2.me/theorems/f307e6d6-8bc6-4795-a6fe-ac78fd019d33
-- title:
--   Proposition 2.1 (2.5), stability term — $\sum_t\mathbb E[C_t(p_t)]$
-- statement:
--   This is the stability term $I_2$ of the four-term decomposition behind the corrupted stochastic bound (2.5) of Proposition 2.1, in its proxy form.
--
--   **Setting.** Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Let $\theta$ satisfy $\|\theta\|_{\mathcal A}\le1$ and have a unique optimal action $a^*$, write $\Delta(a)=(a-a^*)^\top\theta$, and let $\Delta_0\in(0,1]$ satisfy $\Delta_0\le\Delta(a)$ for all $a\ne a^*$. Let $n$ be a feasible sampling allocation of (1.2), with cost $c^n(\mathcal A,\theta)=\sum_an_a\Delta(a)$. Consider an execution of IA-FTRL for $T\ge1$ rounds in the corrupted stochastic regime with budget $C\ge0$, with sampling laws $p_t$ and exponential weights $q_t\propto\exp(-\hat L_{t-1}/\beta_t)$, where $\beta_t=16d+\sqrt{dt/(1+\log K)}$.
--
--   There is an absolute constant $c_0>0$ such that, for every such instance and allocation $n$, there is a constant $M$, independent of $T$, $C$ and the run, with
--   $$
--   \sum_{t=1}^T\mathbb E\big[C_t(p_t)\big]\ \le\ c_0\Big(c^n(\mathcal A,\theta)\log K\cdot\log T+\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C\Big)+M .
--   $$
--
--   Here $C_t(p)=\beta_t\sum_bp_b\sum_aq_{t,a}\,\chi\big((a-\bar a_t)^\top v_b(p)/\beta_t\big)$ is the proxy function of constraint (2.3f), with $\chi(x)=e^x+e^{-x}-2$ and $\bar a_t=\sum_aq_{t,a}a$. It dominates the stability sum, $\mathbb E[D_t]\le\mathbb E[C_t(p_t)]$. In the source, $\sum_t\mathbb E[C_t(p_t)]\le24e^2KC_\beta^7+2c_RE_T$.
--
--   **Formalization Note** The left-hand side is the corresponding term of the regret decomposition (D.167) (`IAFTRL.lemma_D_18`, third inequality, centered at $\theta$ and $a^*$), with 0-based rounds. The paper bounds the term by an instance constant plus a multiple of $c_R E_T$, where $E_T=\sum_tt^{-1/2}P(G_t^c)$ is the good-event failure sum. Lemma C.24 and (C.4) of v1 turn $c_R E_T$ into an instance constant plus $O(c_R\Delta_{\min}^{-128/255})\sqrt C$; $M$ collects all budget-independent constants. The right-hand side has the shape of (2.5) for all three term bounds.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Appendix C.3, Lemma C.3 and (C.37)–(C.40) (p.55), with Lemma C.24 (p.81) and (C.4) (p.50)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_proxyC

namespace IAFTRL

open Matrix MeasureTheory

/-- **Stability contribution in the corrupted stochastic regime.** Zhao–Tan, *Best-of-Both-Worlds
FTRL for Linear Bandits*, arXiv:2611.01299v1, Lemma C.3, (C.37)–(C.40) (with Lemma C.24 and (C.4)):
"`I_2 := Σ_{t=1}^T E[D_t] ≤ Σ_{t=1}^T E[C_t(p_t)] … ≤ 24e² K C_β^7 + 2c_R E_T`". This is the bound on
the proxy sum `Σ_t E[C_t(p_t)]`, which dominates the stability sum `Σ_t E[D_t]`.

**Formalization Note.** Rounds are 0-based: Lean round `t` is the paper's round `t + 1`, with
`q_t = qSoft β_{t+1} arms (Σ_{s<t} θ̂_s)`; the left side is the corresponding term of Lemma D.18
(`IAFTRL.lemma_D_18`, third inequality, at center `θ` and reference action `a*`). The failure-event
sum `c_R E_T` is bounded through Lemma C.24 and (C.4) of v1 (`√n₀ ≤ √N_burn + √C`,
`√T_◦ ≤ √(Q+1) Δ_min^{-5/2} + 32 Δ_min^{-1/2} √n₀`); every budget-independent constant goes into `M`,
chosen after `(d, K, 𝒜, θ, a*, Δ₀, n)` and before the probability space, `T`, `C` and the run.
`c_R = √(d log(eK)) ≤ √3 √(d log K)` for `K ≥ 2`, and `Δ_min^{-1/2}, Δ_min^{-γ₀} ≤ Δ₀^{-128/255}` for
`Δ₀ ≤ min(Δ_min, 1)`, `γ₀ = 128/255` ((C.5e)). All three term bounds use the right-hand side shape of
(2.5); only the exploration term needs the cost term. -/
theorem proposition_2_1_stability : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∑ t ∈ Finset.range T, ∫ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ∂P ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M := by sorry

end IAFTRL
