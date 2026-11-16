-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_24_good_event
-- name    : IAFTRL.lemma_C_24_good_event
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T09:53:18.051452+00:00
-- url     : https://prove2.me/theorems/1d99b999-97f8-43db-b125-94839820dc08
-- title:
--   Lemmas C.24–C.26 (v1) — predictable good events with separation and a $\sqrt C$ weighted failure sum
-- statement:
--   This is the probabilistic core shared by the penalty, stability and exploration terms in the corrupted stochastic analysis of IA-FTRL. It combines the predictable good events of Definition C.25, their separation property (Lemma C.26), and their weighted failure sum (Lemma C.24 with (C.4)).
--
--   **Setting.** Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Let $\theta$ satisfy $\|\theta\|_{\mathcal A}\le1$ with a unique optimal action $a^*$, and let $\Delta_0\in(0,1]$ satisfy $\Delta_0\le(a-a^*)^\top\theta$ for all $a\ne a^*$. Consider an execution of IA-FTRL for $T\ge1$ rounds in the corrupted stochastic regime with budget $C\ge0$, with loss estimates $\hat\theta_s$. Write
--   $$
--   X_{t,a}=(a-a^*)^\top\sum_{s<t}\hat\theta_s
--   $$
--   for the estimated cumulative loss difference before round $t+1$, and $c_R=\sqrt{d\log(eK)}$.
--
--   **Claim.** There is an absolute constant $c_0>0$ such that, for every such instance, there is a constant $M$ (independent of $T$, $C$ and the run) with the following property. Every run admits measurable events $G_0,G_1,\dots$ such that
--
--   1. on $G_t$, for every $t<T$, every suboptimal action is separated from $a^*$:
--   $$
--   X_{t,a}\ge4\,(t+1)^{3/4}\qquad(a\ne a^*);
--   $$
--   2. the weighted failure sum is controlled:
--   $$
--   c_R\sum_{t<T}\frac{P(G_t^{c})}{\sqrt{t+1}}\le c_0\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C+M .
--   $$
--
--   On the good events the FTRL weights concentrate on $a^*$, so the entropy and proxy-function costs decay exponentially (Lemma C.22). Off them, every round costs $O(c_R/\sqrt t)$. Hence this statement is what turns the penalty and stability terms into instance constants plus an $O(\sqrt C)$ corruption term.
--
--   **Formalization Note** Rounds are 0-based (Lean round $t$ is the paper's round $t+1$). The source's separation exponent $\alpha=3/4+13/(10P)$ is replaced by the smaller exponent $3/4$, which suffices for Lemma C.22. The source's bound $2\sqrt{T_\circ}+3A+130\sqrt{n_0}+2K56^P+3c_{\mathrm{tail}}\Delta_{\min}^{-\gamma_0}\sqrt{n_0}$ becomes the displayed one via $n_0=\max\{N_{\mathrm{burn}},\lceil C\rceil\}$, $\sqrt{n_0}\le\sqrt{N_{\mathrm{burn}}}+\sqrt C$, (C.4), $\gamma_0=128/255$, $\Delta_{\min}^{-1/2}\le\Delta_0^{-128/255}$ and $c_R\le\sqrt3\sqrt{d\log K}$ for $K\ge2$. For $K=1$ there is no suboptimal action and $G_t=\Omega$ works.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Definition C.25 and Lemma C.26 (p.81), Lemma C.24 (p.77), (C.4) (p.50), (C.5e)–(C.7) (p.50)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_proxyC
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_Run_cumEst

namespace IAFTRL

open Matrix MeasureTheory

/-- **Predictable good events and their weighted failure sum.** Zhao–Tan, *Best-of-Both-Worlds FTRL
for Linear Bandits*, arXiv:2611.01299v1, Definition C.25, Lemma C.26 and Lemma C.24, with (C.4):
the predictable scalar good event `G_t` satisfies, "On `G_t`, `r_t = a*`, `M_t = 0`, and
`Z_{t,a} = X_{t,a} ≥ 4τ_t ≥ 4t^α (a ≠ a*)`" (Lemma C.26, `α = 3/4 + 13/(10P) ≥ 3/4`), and
"`Σ_{t≥1} t^{-1/2} P(G_t^c) ≤ 2√T_◦ + 3A + 130√n₀ + 2K56P + 3c_tail Δ_min^{-γ₀} √n₀`" (Lemma C.24),
where `n₀ = max{N_burn, ⌈C⌉}` and `√T_◦ ≤ √(Q+1) Δ_min^{-5/2} + 32 Δ_min^{-1/2} √n₀` (C.4).

For every instance of the corrupted stochastic regime there are measurable events `G_t` (Lean
round `t`, paper round `t + 1`) on which every suboptimal action's estimated cumulative loss
difference `X_{t,a} = (a − a*)^⊤ Σ_{s<t} θ̂_s` is at least `4(t + 1)^{3/4}`, and whose weighted failure
sum satisfies `c_R Σ_{t<T} P(G_t^c)/√(t+1) ≤ c₀ √(d log K) Δ₀^{-128/255} √C + M`.

**Formalization Note.** `c₀` is absolute; `M` is chosen after `(d, K, 𝒜, θ, a*, Δ₀)` and before the
probability space, `T`, `C` and the run; the events are chosen after the run. The separation is
stated with the exponent `3/4 ≤ α`. With `c_R = √(d log(eK)) ≤ √3 √(d log K)` for `K ≥ 2`,
`√n₀ ≤ √N_burn + √C` and `Δ_min^{-1/2}, Δ_min^{-γ₀} ≤ Δ₀^{-128/255}` (`γ₀ = 128/255`, `Δ₀ ≤ min(Δ_min, 1)`),
Lemma C.24 gives the displayed bound; for `K = 1` there is no suboptimal action and `G_t = Ω`. -/
theorem lemma_C_24_good_event : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∃ G : ℕ → Set Ω, (∀ t, MeasurableSet (G t)) ∧
            (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar →
              4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) ∧
            cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
              c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
                M := by sorry

end IAFTRL
