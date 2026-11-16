-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_30_local_moments
-- name    : IAFTRL.lemma_C_30_local_moments
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:27:53.781779+00:00
-- url     : https://prove2.me/theorems/274f0a66-65f5-440e-a162-ff0f93431eea
-- title:
--   Lemmas C.14, C.24, C.26, C.30 (v1) — good events with per-action inverse and positive local moments
-- statement:
--   This is the probabilistic core of the corrupted stochastic analysis of IA-FTRL, stated **one action at a time**: predictable good events, their separation and failure sum, and the inverse and positive local moments of the estimated cumulative loss differences on those events.
--
--   **Setting.** Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Let $\theta$ satisfy $\|\theta\|_{\mathcal A}\le1$ with a unique optimal action $a^*$, gaps $\Delta(a)=(a-a^*)^\top\theta$, and let $\Delta_0\in(0,1]$ satisfy $\Delta_0\le\Delta(a)$ for all $a\ne a^*$. Consider an execution of IA-FTRL for $T\ge1$ rounds in the corrupted stochastic regime with budget $C\ge0$, with loss estimates $\hat\theta_s$. Write
--   $$
--   X_{t,a}=(a-a^*)^\top\sum_{s<t}\hat\theta_s
--   $$
--   for the estimated cumulative loss difference before round $t+1$, and $c_R=\sqrt{d\log(eK)}$.
--
--   **Claim.** There is an absolute constant $c_0>0$ such that, for every such instance, there is a constant $M$ (independent of $T$, $C$ and the run) with the following property. For every run there are a moment order $P\in\mathbb N$ with $P\ge8$ and $K\le2^P$, measurable events $G_0,G_1,\dots$ and numbers $\Psi_t\ge1$ such that, for all $t<T$ and all $a\ne a^*$:
--
--   1. on $G_t$: $X_{t,a}\ge4\,(t+1)^{3/4}$;
--   2. $\displaystyle c_R\sum_{t<T}\frac{P(G_t^{c})}{\sqrt{t+1}}\le c_0\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C+M$;
--   3. (inverse local moment) $\displaystyle E\Big[\mathbf 1_{G_t}\Big(\frac{(t+1)\Delta(a)}{X_{t,a}}\Big)^P\Big]\le 8^P$;
--   4. (positive local moment) $\displaystyle E\Big[\mathbf 1_{G_t}\Big(\frac{X_{t,a}}{(t+1)\Delta(a)}\Big)^P\Big]\le (8\Psi_t)^P$;
--   5. (bounded distortion) $\Psi_t\le M$ and $\displaystyle\sum_{t<T}\frac{\Psi_t-1}{t+1}\le M$,
--
--   where the random variables in 3–4 are integrable.
--
--   In the source, $P=2\lceil256+\log(2K)\rceil$, so $K^{1/P}<2$. The events are those of Definition C.25 and are empty before $T_\circ$. Item 3 is the single-action form of (C.114a)–(C.114c), from Lemma C.30 and $X_{t,a}\ge\frac12Y^\dagger_{t,a}$ on $G_t$. Item 4 is the single-action form of (C.114d)–(C.114e), from Lemma C.14 and $X_{t,a}\le Y^\dagger_{t,a}$. The quantity $\Psi_t=1+A_0u_0^{1-\kappa_0}\Delta_{\min}^{-1}(n_0/t)^{\sigma_0}$ of (C.118) satisfies $\Psi_t\le\Psi_{\Delta_{\min}}$ and $\sum_{t\ge T_\circ}(\Psi_t-1)/t\le3A_0\Delta_{\min}^{-\varepsilon_0}$.
--
--   Lemma C.13's moment bounds on the gap ratios $L_t,U_t$ (`IAFTRL.lemma_C_13_good_event`) follow from these per-action bounds by a short argument: maximum-to-sum, the $P$-th root trick using $K\le2^P$, and generalized Hölder. So this statement is the remaining analytic content of the good-event layer.
--
--   **Formalization Note** Rounds are 0-based (Lean round $t$ is the paper's round $t+1$). The moment order is called `p` in Lean, to avoid a clash with the measure `P`. $P$, the events and $\Psi$ are chosen after the run, while $c_0$ is absolute and $M$ depends only on the instance. Items 1–2 are exactly the conclusion of `IAFTRL.lemma_C_24_good_event`. For $t<T_\circ$ one may take $\Psi_t=1$, since $G_t=\emptyset$ there. For $K=1$ there is no suboptimal action and $G_t=\Omega$ works.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Definition C.17 (p.71), (C.113)–(C.114) in Lemma C.13 (p.66), Lemma C.14 (p.67), Lemma C.24 (p.77), Definition C.25 and Lemma C.26 (p.78), Lemma C.30 (p.82)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_Run_cumEst

namespace IAFTRL

open Matrix MeasureTheory

/-- **Predictable good events with per-action local moments.** Zhao–Tan, *Best-of-Both-Worlds FTRL
for Linear Bandits*, arXiv:2611.01299v1, Definition C.17 (`P = 2⌈256 + log(2K)⌉`, `k = K^{1/P}`),
Definition C.25, Lemma C.26 and Lemma C.24 with (C.4) (the good events, their separation and their
weighted failure sum), Lemma C.30 with (C.113)–(C.114c) (inverse local moments:
"`E[1_{G_t} L_t^P] ≤ 1 + Σ_{a≠a*} (2tΔ(a))^P E[I_t (Y†_{t,a})^{-P}] ≤ 1 + K8^P`"), and Lemma C.14 with
(C.114d)–(C.114e) (positive local moments: "`E[1_{G_t} (X_{t,a}/(tΔ(a)))^P] ≤ E[I_t (Y†_{t,a}/(tΔ(a)))^P]
≤ (8Ψ_t)^P`", "`Ψ_t ≤ Ψ_{Δmin}`, `Σ_{t≥T◦}(Ψ_t − 1)/t ≤ 3A₀Δ_min^{-ε₀}`"), with `G_t = ∅` for `t < T◦`.

For every instance of the corrupted stochastic regime there are an even moment order `P ≥ 8` with
`K ≤ 2^P`, measurable events `G_t` (Lean round `t`, paper round `t + 1`) and numbers `Ψ_t ≥ 1` such
that, with `X_{t,a} = (a − a*)^⊤ Σ_{s<t} θ̂_s`:
1. on `G_t`, `X_{t,a} ≥ 4(t + 1)^{3/4}` for `a ≠ a*`;
2. `c_R Σ_{t<T} P(G_t^c)/√(t+1) ≤ c₀ √(d log K) Δ₀^{-128/255} √C + M`;
3. `E[1_{G_t} ((t+1)Δ(a)/X_{t,a})^P] ≤ 8^P` for `a ≠ a*` (inverse local moment);
4. `E[1_{G_t} (X_{t,a}/((t+1)Δ(a)))^P] ≤ (8Ψ_t)^P` for `a ≠ a*` (positive local moment);
5. `Ψ_t ≤ M` and `Σ_{t<T} (Ψ_t − 1)/(t+1) ≤ M` (bounded accumulated distortion).

**Formalization Note.** `c₀` is absolute; `M` is chosen after `(d, K, 𝒜, θ, a*, Δ₀)` and before the
probability space, `T`, `C` and the run; `P`, the events and `Ψ` are chosen after the run (in the
source `P` depends only on `K`, and `K^{1/P} = k < 2`). Items 1–2 are those of
`IAFTRL.lemma_C_24_good_event`. Item 3 is (C.114a)–(C.114c) for a single action; item 4 is
(C.114d)–(C.114e) for a single action, with `Ψ_t` of (C.118); `Ψ_t := 1` for `t < T◦`, where
`G_t = ∅`. The integrands are stated with their integrability. -/
theorem lemma_C_30_local_moments : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∃ (G : ℕ → Set Ω) (p : ℕ) (Ψ : ℕ → ℝ), (∀ t, MeasurableSet (G t)) ∧
            8 ≤ p ∧ (K : ℝ) ≤ 2 ^ p ∧
            (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar →
              4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) ∧
            cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
              c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
                M ∧
            (∀ t < T, ∀ a, a ≠ jstar →
              Integrable ((G t).indicator fun ω => ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
                ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) P ∧
              ∫ ω, (G t).indicator (fun ω => ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
                ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) ω ∂P ≤ 8 ^ p) ∧
            (∀ t < T, ∀ a, a ≠ jstar →
              Integrable ((G t).indicator fun ω => ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
                ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) P ∧
              ∫ ω, (G t).indicator (fun ω => ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
                ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) ω ∂P ≤ (8 * Ψ t) ^ p) ∧
            (∀ t < T, 1 ≤ Ψ t ∧ Ψ t ≤ M) ∧
            ∑ t ∈ Finset.range T, (Ψ t - 1) / (t + 1) ≤ M := by sorry

end IAFTRL
