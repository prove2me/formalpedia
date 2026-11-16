-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_34_interface
-- name    : IAFTRL.lemma_C_34_interface
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:41:19.355966+00:00
-- url     : https://prove2.me/theorems/c5d8e9df-7bde-41a8-8f8b-2bcccf3873bf
-- title:
--   Lemma C.34 (v1) — the full-history scalar difference interface of IA-FTRL
-- statement:
--   This lemma translates the constraints of the IA-FTRL program into conditional properties of the observed increments of the estimated cumulative loss differences. These are the only properties of the learner used by the scalar moment analysis of the source (Appendix C.6).
--
--   **Setting.** Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Consider an execution of IA-FTRL for $T$ rounds against an adaptive environment. Round $t$ has pre-action $\sigma$-algebra $\mathcal G_t$, loss vector $\theta_t$, sampling law $p_t$, played action $A_t$, feedback $Y_t\in[-1,1]$ and loss estimate $\hat\theta_t=Y_t\,M(p_t)^{-1}A_t$, where $M(p)=\sum_bp_b\,bb^\top$. Fix any action $a^*$, and write
--   $$
--   D_{t,a}=(a-a^*)^\top\hat\theta_t ,\qquad Z_{t,a}=\Big(a-r_t\Big)^\top\sum_{s<t}\hat\theta_s ,
--   $$
--   where $r_t$ is the action minimizing the cumulative estimate (the program's reference). Let $\beta_t=16d+\sqrt{dt/(1+\log K)}$ and $B=2^{25}\lceil256+\log(2K)\rceil$.
--
--   **Claim.** For every round $t$ (paper indexing) and every action $a$:
--
--   1. $D_{t,a}$ is measurable with respect to $\mathcal G_{t+1}$;
--   2. $E[D_{t,a}\mid\mathcal G_t]=(a-a^*)^\top\theta_t$ almost surely;
--   3. $|D_{t,a}|\le2\beta_t+(Z_{t,a}+Z_{t,a^*})/B$ on every history;
--   4. $E[D_{t,a}^2\mid\mathcal G_t]\le4\beta_t+2(Z_{t,a}^2+Z_{t,a^*}^2)/(Bt)$ almost surely.
--
--   Item 2 is the difference unbiasedness of the executed reconstruction: $\sum_bp_{t,b}v_{t,b}b^\top=I_d$, so $E[g_{t,a}-g_{t,b}\mid\mathcal G_t]=(a-b)^\top\theta_t$ for $g_{t,a}=(a-r_t)^\top v_{t,A_t}Y_t$. Items 3 and 4 combine $D_{t,a}=g_{t,a}-g_{t,a^*}$ with the update-magnitude and second-moment constraints (2.3d) and (2.3e) of the selected law. Together they are the interface (C.226)–(C.228) on which the source's good-event and moment analysis rests.
--
--   **Formalization Note** Rounds are 0-based (Lean round $t$ is the paper's round $t+1$, so $\beta_{t+1}$ and $B(t+1)$ appear). $Z_{t,a}$ is `Zd arms (R.cumEst arms t ω) a`. Conditional expectations are taken with respect to the pre-action $\sigma$-algebra `R.G t` of `IsIAFTRLRun`. Measurability is also stated with respect to the ambient $\sigma$-algebra.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Lemma C.34 ((C.226)–(C.229), p.87), Lemma C.20 and Lemma C.18 (p.71–73)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_Zd
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_Run_cumEst
import Definitions.Def_IAFTRL_Run_thetaHat

namespace IAFTRL

open Matrix MeasureTheory

/-- **The full-history scalar difference interface of IA-FTRL.** Zhao–Tan, *Best-of-Both-Worlds FTRL
for Linear Bandits*, arXiv:2611.01299v1, Lemma C.34 ((C.226)–(C.228), (C.229)), from Lemma C.20
("`E_{t−1}[g_{t,a} − g_{t,b}] = (a − b)^⊤θ_t`, `E_{t−1}[g²_{t,a}] ≤ V_{t,a}`, `|g_{t,a}| ≤ U_{t,a}`") and
Lemma C.18: for any fixed action `a*`, the increments `D_{t,a} = g_{t,a} − g_{t,a*} = (a − a*)^⊤ θ̂_t` of
the estimated cumulative loss differences satisfy, for every round of an IA-FTRL run,
1. `D_{t,a}` is measurable after the round (w.r.t. the next pre-action σ-algebra and the ambient one);
2. `E[D_{t,a} | G_t] = (a − a*)^⊤ θ_t` (difference unbiasedness, (C.229a));
3. `|D_{t,a}| ≤ 2β_t + (Z_{t,a} + Z_{t,a*})/B` (update magnitude, (C.229b)–(C.229c));
4. `E[D²_{t,a} | G_t] ≤ 4β_t + 2(Z²_{t,a} + Z²_{t,a*})/(Bt)` (second moment, (C.229d)–(C.229f)),
where `Z_{t,a} = Zd arms (Σ_{s<t} θ̂_s) a` is the program's reference gap and `G_t` the pre-action
σ-algebra.

**Formalization Note.** Rounds are 0-based: Lean round `t` is the paper's round `t + 1`, so `β_{t+1}`
and `B(t + 1)` appear. `M_t = Z_{t,a*}` in the source's notation. The identities hold for every
fixed `a*` (no optimality is used). Item 2 uses `P(A_t = b | G_t) = p_{t,b}`,
`E[Y_t | G_t ∨ σ(A_t)] = A_t^⊤θ_t` and `Σ_b p_{t,b} v_{t,b} b^⊤ = I_d` (the design matrix of a feasible
`p_t` is invertible on a spanning action set); items 3–4 use `|Y_t| ≤ 1` and the constraints
(2.3d)–(2.3e) of the selected law. -/
theorem lemma_C_34_interface {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) (jstar : Fin K) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) :
    ∀ t < T, ∀ a : Fin K,
      (Measurable[R.G (t + 1)] (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ∧
        Measurable (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω)) ∧
      P[fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω | R.G t] =ᵐ[P]
        (fun ω => (arms a - arms jstar) ⬝ᵥ R.θs t ω) ∧
      (∀ ω, |(arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω| ≤ 2 * beta d K (t + 1) +
        (Zd arms (R.cumEst arms t ω) a + Zd arms (R.cumEst arms t ω) jstar) / Bc K) ∧
      P[fun ω => ((arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ^ 2 | R.G t] ≤ᵐ[P]
        (fun ω => 4 * beta d K (t + 1) + 2 * (Zd arms (R.cumEst arms t ω) a ^ 2 +
          Zd arms (R.cumEst arms t ω) jstar ^ 2) / (Bc K * ((t : ℝ) + 1))) := by sorry

end IAFTRL
