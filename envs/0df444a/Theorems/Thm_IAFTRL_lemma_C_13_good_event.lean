-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_13_good_event
-- name    : IAFTRL.lemma_C_13_good_event
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:05:28.769517+00:00
-- url     : https://prove2.me/theorems/b6d62c9f-1090-485f-a1d5-49d2eaaafd5f
-- title:
--   Lemmas C.13, C.14, C.24 (v1) — good events with empirical gap-ratio moments
-- statement:
--   This is the probabilistic core of the corrupted stochastic analysis of IA-FTRL, now with the **empirical gap ratios** that the exploration term needs. It extends `IAFTRL.lemma_C_24_good_event` (items 1–2 below) by the gap-ratio moment bounds of Definition C.12, Lemma C.13 and Lemma C.14, which live on the same good events.
--
--   **Setting.** Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Let $\theta$ satisfy $\|\theta\|_{\mathcal A}\le1$ with a unique optimal action $a^*$, gaps $\Delta(a)=(a-a^*)^\top\theta$, and let $\Delta_0\in(0,1]$ satisfy $\Delta_0\le\Delta(a)$ for all $a\ne a^*$. Consider an execution of IA-FTRL for $T\ge1$ rounds in the corrupted stochastic regime with budget $C\ge0$, with loss estimates $\hat\theta_s$. Write
--   $$
--   X_{t,a}=(a-a^*)^\top\sum_{s<t}\hat\theta_s ,\qquad \hat\Delta_{t}(a)=\min\Big\{2,\ \frac{Z_{t,a}}{t+1}\Big\}
--   $$
--   for the estimated cumulative loss difference and the empirical gap (2.2) before round $t+1$, and $c_R=\sqrt{d\log(eK)}$.
--
--   **Claim.** There is an absolute constant $c_0>0$ such that, for every such instance, there is a constant $M$ (independent of $T$, $C$ and the run) with the following property. Every run admits measurable events $G_0,G_1,\dots$ and random variables $L_t,U_t$ such that, for all $t<T$:
--
--   1. on $G_t$: $X_{t,a}\ge4\,(t+1)^{3/4}$ for every $a\ne a^*$;
--   2. $\displaystyle c_R\sum_{t<T}\frac{P(G_t^{c})}{\sqrt{t+1}}\le c_0\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C+M$;
--   3. on $G_t$: $L_t\ge1$, $U_t\ge0$, $(t+1)\Delta(a)\le L_tX_{t,a}$ for $a\ne a^*$, and for every arm
--   $$
--   \Delta(a)\le L_t\,\hat\Delta_t(a),\qquad \hat\Delta_t(a)\le U_t\,\Delta(a);
--   $$
--   4. $E[\mathbf 1_{G_t}L_t^8]\le c_0$;
--   5. $E[\mathbf 1_{G_t}L_tU_t]\le M$;
--   6. $\displaystyle\sum_{t<T}\frac{E[\mathbf 1_{G_t}L_t^3U_t]}{t+1}\le c_0\,(1+\log T)+M$,
--
--   where all three random variables in 4–6 are integrable.
--
--   In the source, $L_t=\max\{1,\max_{a\ne a^*}t\Delta(a)/X_{t,a}\}$ and $U_t=\max_{a\ne a^*}\hat\Delta_t(a)/\Delta(a)$ on $G_t$ (Definition C.12). Lemma C.13 gives $\|\mathbf 1_{G_t}L_t\|_P\le25$, $E[\mathbf 1_{G_t}L_tU_t]\le400\Psi_t$, $E[\mathbf 1_{G_t}L_t^3U_t]\le250000\Psi_t$, and the two gap comparisons. Lemma C.14 gives $\Psi_t\le\Psi_{\Delta_{\min}}$ and $\sum_{t\ge T_\circ}(\Psi_t-1)/t\le3A_0\Delta_{\min}^{-\varepsilon_0}$. The good events are empty before $T_\circ$.
--
--   Together with the feasibility of the comparison law built from $n$ (Lemma C.10, already proved), these bounds turn the exploration term into $O(B\,c^n\log T)$ plus instance constants plus $O(\sqrt C)$ (Lemmas C.6 and C.9).
--
--   **Formalization Note** Rounds are 0-based (Lean round $t$ is the paper's round $t+1$), so $\hat\Delta_t$ is `gapHat arms (t + 1) (R.cumEst arms t ω)`. Item 4 follows from $\|\mathbf 1_{G_t}L_t\|_P\le25$ with $P\ge512\ge8$ (Lyapunov), so $c_0\ge25^8$. Item 5 uses $400\Psi_t\le400\Psi_{\Delta_{\min}}$. Item 6 uses $250000\sum_{t\le T}\Psi_t/t\le250000(\log(eT)+3A_0\Delta_{\min}^{-\varepsilon_0})$. The separation exponent $\alpha=3/4+13/(10P)$ is relaxed to $3/4$. Items 1–2 are exactly the conclusion of `IAFTRL.lemma_C_24_good_event`. They are restated because the ratios must live on the same events. For $K=1$, take $G_t=\Omega$, $L_t=1$, $U_t=0$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Definition C.12 and Lemma C.13 (p.65–66), Lemma C.14 (p.67), Definition C.25 and Lemma C.26 (p.81), Lemma C.24 (p.77), (C.4)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_gapHat
import Definitions.Def_IAFTRL_Run_cumEst

namespace IAFTRL

open Matrix MeasureTheory

/-- **Predictable good events with empirical gap-ratio moments.** Zhao–Tan, *Best-of-Both-Worlds
FTRL for Linear Bandits*, arXiv:2611.01299v1, Definition C.25, Lemma C.26 and Lemma C.24 with (C.4)
(the good events, their separation and their weighted failure sum), Definition C.12 and Lemma C.13
("For `t ≥ T◦`, `‖1_{G_t}L_t‖_P ≤ 25`, `E[1_{G_t}L_tU_t] ≤ 400Ψ_t`, `E[1_{G_t}L_t³U_t] ≤ 250000Ψ_t` …
On `G_t`, `Δ(a) ≤ L_tΔ̂_t(a) ≤ L_tU_tΔ(a)` for every arm"), and Lemma C.14
(`Ψ_t ≤ Ψ_{Δmin}`, `Σ_{t≥T◦}(Ψ_t − 1)/t ≤ 3A₀Δ_min^{-ε₀}`), with `G_t = ∅` for `t < T◦`.

For every instance of the corrupted stochastic regime there are measurable events `G_t` (Lean round
`t`, paper round `t + 1`) and random variables `L_t, U_t` (the gap ratios
`L_t = max{1, max_{a≠a*} tΔ(a)/X_{t,a}}`, `U_t = max_{a≠a*} Δ̂_t(a)/Δ(a)` of Definition C.12) such that:
1. on `G_t`, `X_{t,a} = (a − a*)^⊤ Σ_{s<t} θ̂_s ≥ 4(t + 1)^{3/4}` for `a ≠ a*`;
2. `c_R Σ_{t<T} P(G_t^c)/√(t+1) ≤ c₀ √(d log K) Δ₀^{-128/255} √C + M`;
3. on `G_t`, `L_t ≥ 1`, `U_t ≥ 0`, `(t+1)Δ(a) ≤ L_t X_{t,a}` for `a ≠ a*`, and, for every arm,
   `Δ(a) ≤ L_t Δ̂(a)` and `Δ̂(a) ≤ U_t Δ(a)` (with `Δ̂ = Δ̂_{t+1}` at the cumulative estimate);
4. `E[1_{G_t} L_t^8] ≤ c₀`;
5. `E[1_{G_t} L_t U_t] ≤ M`;
6. `Σ_{t<T} E[1_{G_t} L_t³ U_t]/(t+1) ≤ c₀ (1 + log T) + M`.

**Formalization Note.** `c₀` is absolute; `M` is chosen after `(d, K, 𝒜, θ, a*, Δ₀)` and before the
probability space, `T`, `C` and the run; the events and ratios are chosen after the run. Item 4 is
`‖1_{G_t}L_t‖_P ≤ 25` with `P ≥ 512 ≥ 8` (Lyapunov). Item 5 is `400Ψ_t ≤ 400Ψ_{Δmin}`. Item 6 is
`250000 Σ_{t ≤ T} Ψ_t/t ≤ 250000(log(eT) + 3A₀Δ_min^{-ε₀})`. Items 1–2 are those of
`IAFTRL.lemma_C_24_good_event` (separation exponent `3/4 ≤ α`); they are restated because the gap
ratios live on the same events. For `K = 1` take `G_t = Ω`, `L_t = 1`, `U_t = 0`. -/
theorem lemma_C_13_good_event : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∃ (G : ℕ → Set Ω) (L U : ℕ → Ω → ℝ), (∀ t, MeasurableSet (G t)) ∧
            (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar →
              4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) ∧
            cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
              c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
                M ∧
            (∀ t < T, ∀ ω ∈ G t, 1 ≤ L t ω ∧ 0 ≤ U t ω ∧
              (∀ a, a ≠ jstar → (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) ≤
                L t ω * ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ∧
              ∀ a, (arms a - arms jstar) ⬝ᵥ θ ≤
                  L t ω * gapHat arms (t + 1) (R.cumEst arms t ω) a ∧
                gapHat arms (t + 1) (R.cumEst arms t ω) a ≤
                  U t ω * ((arms a - arms jstar) ⬝ᵥ θ)) ∧
            (∀ t < T, Integrable ((G t).indicator fun ω => L t ω ^ 8) P ∧
              ∫ ω, (G t).indicator (fun ω => L t ω ^ 8) ω ∂P ≤ c₀) ∧
            (∀ t < T, Integrable ((G t).indicator fun ω => L t ω * U t ω) P ∧
              ∫ ω, (G t).indicator (fun ω => L t ω * U t ω) ω ∂P ≤ M) ∧
            (∀ t < T, Integrable ((G t).indicator fun ω => L t ω ^ 3 * U t ω) P) ∧
            ∑ t ∈ Finset.range T,
                (∫ ω, (G t).indicator (fun ω => L t ω ^ 3 * U t ω) ω ∂P) / (t + 1) ≤
              c₀ * (1 + Real.log T) + M := by sorry

end IAFTRL
