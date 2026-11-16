-- Prove2me | Theorems.Thm_IAFTRL_proposition_2_1_exploration
-- name    : IAFTRL.proposition_2_1_exploration
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T09:30:22.803488+00:00
-- url     : https://prove2.me/theorems/5ecd9766-2074-4e99-906c-c4e05f601d75
-- title:
--   Proposition 2.1 (2.5), exploration term — $\sum_t\mathbb E[\langle p_t-q_t,\Delta\rangle]$
-- statement:
--   This is the exploration term $I_3$ of the four-term decomposition behind the corrupted stochastic bound (2.5) of Proposition 2.1, and the term that carries the information-acquisition cost.
--
--   **Setting.** Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Let $\theta$ satisfy $\|\theta\|_{\mathcal A}\le1$ and have a unique optimal action $a^*$, write $\Delta(a)=(a-a^*)^\top\theta$, and let $\Delta_0\in(0,1]$ satisfy $\Delta_0\le\Delta(a)$ for all $a\ne a^*$. Let $n$ be a feasible sampling allocation of (1.2), with cost $c^n(\mathcal A,\theta)=\sum_an_a\Delta(a)$. Consider an execution of IA-FTRL for $T\ge1$ rounds in the corrupted stochastic regime with budget $C\ge0$, with sampling laws $p_t$ and exponential weights $q_t\propto\exp(-\hat L_{t-1}/\beta_t)$, where $\beta_t=16d+\sqrt{dt/(1+\log K)}$.
--
--   There is an absolute constant $c_0>0$ such that, for every such instance and allocation $n$, there is a constant $M$, independent of $T$, $C$ and the run, with
--   $$
--   I_3:=\sum_{t=1}^T\mathbb E\big[\langle p_t-q_t,\Delta\rangle\big]\ \le\ c_0\Big(c^n(\mathcal A,\theta)\log K\cdot\log T+\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C\Big)+M .
--   $$
--
--   Here $\langle p_t-q_t,\Delta\rangle=\sum_a(p_{t,a}-q_{t,a})\Delta(a)$ is the regret paid for exploring beyond the FTRL update. In the source, $I_3\le2^{22}Bc^n\log(eT)+M_{3,n}+8c_RE_T$ with $B=2\lceil256+\log(2K)\rceil\le2048\log(eK)$. This rests on the objective comparison with a feasible distribution built from the allocation $n$ after a horizon-independent burn-in.
--
--   **Formalization Note** The left-hand side is the corresponding term of the regret decomposition (D.167) (`IAFTRL.lemma_D_18`, third inequality, centered at $\theta$ and $a^*$), with 0-based rounds. The paper bounds the term by an instance constant plus a multiple of $c_R E_T$, where $E_T=\sum_tt^{-1/2}P(G_t^c)$ is the good-event failure sum. Lemma C.24 and (C.4) of v1 turn $c_R E_T$ into an instance constant plus $O(c_R\Delta_{\min}^{-128/255})\sqrt C$; $M$ collects all budget-independent constants. The right-hand side has the shape of (2.5) for all three term bounds.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Appendix C.4, Lemma C.6 (p.57), with Lemma C.24 (p.81), (C.4) (p.50) and (B.4) (p.44)

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

/-- **Exploration contribution in the corrupted stochastic regime.** Zhao–Tan, *Best-of-Both-Worlds
FTRL for Linear Bandits*, arXiv:2611.01299v1, Lemma C.6 (with Lemma C.24, (C.4) and (B.4)): "Fix a
finite feasible sampling allocation `n`. … `I_3 := Σ_{t=1}^T E[⟨p_t − q_t, Δ⟩] ≤ 2^22 B c^n log(eT) +
M_{3,n} + 8c_R E_T`", with `B = 2⌈256 + log(2K)⌉ ≤ 2048 log(eK)` (B.4). The term
`2^22 B c^n log(eT) = 2^22 B c^n (1 + log T)` gives `O(c^n log K · log T)` for `K ≥ 2` and puts the
`T`-free part `2^22 B c^n` into `M`.

**Formalization Note.** Rounds are 0-based: Lean round `t` is the paper's round `t + 1`, with
`q_t = qSoft β_{t+1} arms (Σ_{s<t} θ̂_s)`; the left side is the corresponding term of Lemma D.18
(`IAFTRL.lemma_D_18`, third inequality, at center `θ` and reference action `a*`). The failure-event
sum `c_R E_T` is bounded through Lemma C.24 and (C.4) of v1 (`√n₀ ≤ √N_burn + √C`,
`√T_◦ ≤ √(Q+1) Δ_min^{-5/2} + 32 Δ_min^{-1/2} √n₀`); every budget-independent constant goes into `M`,
chosen after `(d, K, 𝒜, θ, a*, Δ₀, n)` and before the probability space, `T`, `C` and the run.
`c_R = √(d log(eK)) ≤ √3 √(d log K)` for `K ≥ 2`, and `Δ_min^{-1/2}, Δ_min^{-γ₀} ≤ Δ₀^{-128/255}` for
`Δ₀ ≤ min(Δ_min, 1)`, `γ₀ = 128/255` ((C.5e)). All three term bounds use the right-hand side shape of
(2.5); only the exploration term needs the cost term. -/
theorem proposition_2_1_exploration : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∑ t ∈ Finset.range T, ∫ ω, ∑ a, (R.p t ω a -
              qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) *
            ((arms a - arms jstar) ⬝ᵥ θ) ∂P ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M := by sorry

end IAFTRL
