-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_10
-- name    : IAFTRL.lemma_C_10
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T10:26:39.506231+00:00
-- url     : https://prove2.me/theorems/0acc8031-35e8-4697-93f4-c3e27f3dd2e0
-- title:
--   Lemma C.10 (v1) — the comparison law built from a feasible allocation is feasible for (2.3)
-- statement:
--   This is the feasibility step behind the objective comparison in the exploration analysis of IA-FTRL: on good histories, mixing the FTRL weights with a scaled copy of a fixed feasible sampling allocation produces a law that satisfies every constraint of the sampling program (2.3).
--
--   **Setting.** Let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in $\mathbb R^d$ ($d\ge1$), let $\theta$ satisfy $\|\theta\|_{\mathcal A}\le1$ with optimal action $a^*$, and let $\Delta_0\in(0,1]$ satisfy $\Delta_0\le\Delta(a)=(a-a^*)^\top\theta$ for $a\ne a^*$. Let $n$ be a feasible sampling allocation of (1.2) with total mass $N_n$. Fix a round $t$ and a cumulative estimate $S=\sum_{s<t}\hat\theta_s$, write $X_a=(a-a^*)^\top S$, $q_t$ for the exponential weights at rate $\beta_t$, $B$ for the platform constant `Bc K`, and $C_\beta=16d+\sqrt{d/\log(eK)}$. Assume:
--
--   1. $t\ge(32C_\beta)^8$ and $t\ge(4C_\beta\log(eK))^4$;
--   2. the separation $X_a\ge4t^{3/4}$ for every $a\ne a^*$;
--   3. a number $L\ge1$ with $t\Delta(a)\le L\,X_a$ for $a\ne a^*$, and
--   $$
--   L^2\le\frac{\sqrt t}{a_n},\qquad L^2\le\frac{t}{a_{\Delta_0}},\qquad a_n=\max\Big\{1,\frac{4BC_\beta N_n}{d}\Big\},\quad a_{\Delta_0}=\frac{64B}{\Delta_0^2}.
--   $$
--
--   Set $\rho=16BL^2/t$, $w_a=\rho\,n_a\mathbf 1\{a\ne a^*\}$, $\gamma=\sum_aw_a$. Then the comparison law
--   $$
--   p^c=(1-\gamma)\,q_t+w
--   $$
--   is feasible for (2.3) at round $t$. That is, it satisfies the mixture constraint $\gamma\le\Gamma_t$, the update-magnitude constraint (2.3d), the second-moment constraint (2.3e) and the exponential proxy constraint $C_t(p^c)\le2d/\beta_t$, all with the reconstruction $v_b=M(p^c)^{-1}b$.
--
--   The objective comparison $\langle p_t,\hat\Delta_t\rangle\le\langle p^c,\hat\Delta_t\rangle$ then charges the learner only $O(c^n/t)$ per round on good histories, which produces the $c^n\log T$ term of (2.5).
--
--   **Formalization Note** In the source, $L=\mathcal L_t=\max\{1,\max_{a\ne a^*}t\Delta(a)/X_{t,a}\}$ and the hypotheses describe the event $\mathcal W_t=\mathcal G_t\cap\{\mathcal L_t^2\le\sqrt t/a_n\}\cap\{\mathcal L_t^2\le t/a_{\Delta_{\min}}\}$ with $t\ge T_\circ$. Here any $L$ with the stated properties is allowed, $\Delta_{\min}$ is replaced by $\Delta_0$, and the separation $X_{t,a}\ge4\tau_t\ge4t^\alpha$ is used only with the smaller exponent $3/4$. $\log(eK)$ is written $1+\log K$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Lemma C.10 (p.61), with the construction (C.57) and the thresholds (C.58)–(C.62) (p.58)

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocMass
import Definitions.Def_IAFTRL_IsFeasible2_3

namespace IAFTRL

open Matrix

/-- **Lemma C.10 (feasibility of the comparison distribution built from the allocation `n`).**
Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299v1, Lemma C.10 (p.61) with
(C.57) (p.58): "On `𝒲_t` with `t ≥ T_◦`, the above distribution admits a covariance reconstruction
satisfying every constraint of (3.3)", where `ρ_t = 16B𝓛_t²/t`,
`𝒲_t = 𝒢_t ∩ {𝓛_t² ≤ √t/a_n} ∩ {𝓛_t² ≤ t/a_{Δmin}}`, `a_n = max{1, 4BC_βN_n/d}`,
`a_{Δmin} = 64BΔ_min^{-2}`, `w^c_{t,a} = ρ_t n_a 1{a ≠ a*}`, `γ^c_t = Σ_a w^c_{t,a}`,
`p^c_t = (1 − γ^c_t)q_t + w^c_t`, and `T_◦` includes `t ≥ (32C_β)^8` and `t ≥ (4C_β log(eK))^4`.

Fix a feasible sampling allocation `n` of (1.2), a paper round `t` and a cumulative estimate
`S = Σ_{s<t} θ̂_s`, and write `X_a = (a − a*)^⊤S` and `Δ(a) = (a − a*)^⊤θ`. Suppose
`t ≥ (32C_β)^8`, `t ≥ (4C_β log(eK))^4`, the separation `X_a ≥ 4t^{3/4}` holds for `a ≠ a*`, and
`L ≥ 1` satisfies `tΔ(a) ≤ L X_a` for `a ≠ a*`, `L² ≤ √t/a_n` and `L² ≤ t/a_{Δ₀}`. Then the
comparison law `p^c = (1 − γ^c)q_t + w^c` with `w^c_a = ρ n_a 1{a ≠ a*}`, `ρ = 16BL²/t`, is feasible
for program (2.3) at round `t`.

**Formalization Note.** `C_β = 16d + √(d/(1 + log K))` and `log(eK) = 1 + log K` (the platform's
`β_t = 16d + √(dt/(1 + log K))`). The paper's `𝓛_t = max{1, max_{a≠a*} tΔ(a)/X_{t,a}}` is replaced by
any `L ≥ 1` with `tΔ(a) ≤ L X_a`; on `𝒢_t` the separation `X_{t,a} ≥ 4τ_t ≥ 4t^α` is used with the
smaller exponent `3/4 ≤ α`; `Δ_min` is replaced by any `Δ₀ ∈ (0, 1]` below the gaps
(`a_{Δ₀} = 64B/Δ₀² ≥ a_{Δmin}`). The reconstruction is the platform's `vCoef` (`v_b = M(p)^{-1}b`). -/
theorem lemma_C_10 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (hθ : actionNorm arms θ ≤ 1) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar)
    (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1)
    (hgap : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ)
    (n : Fin K → ℝ) (hn : IsFeasibleAlloc arms θ jstar n)
    (t : ℕ) (S : Fin d → ℝ) (L : ℝ)
    (hT1 : (32 * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)))) ^ 8 ≤ t)
    (hT2 : (4 * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K))) * (1 + Real.log K)) ^ 4 ≤ t)
    (hsep : ∀ a, a ≠ jstar → 4 * (t : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ S)
    (hL1 : 1 ≤ L)
    (hLX : ∀ a, a ≠ jstar →
      t * ((arms a - arms jstar) ⬝ᵥ θ) ≤ L * ((arms a - arms jstar) ⬝ᵥ S))
    (hLn : L ^ 2 ≤ Real.sqrt t / max 1
      (4 * Bc K * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K))) * allocMass n / d))
    (hLΔ : L ^ 2 ≤ t / (64 * Bc K / Δ₀ ^ 2)) :
    IsFeasible2_3 arms t S (fun a =>
      (1 - ∑ b, (if b = jstar then 0 else 16 * Bc K * L ^ 2 / t * n b)) *
          qSoft (beta d K t) arms S a +
        (if a = jstar then 0 else 16 * Bc K * L ^ 2 / t * n a)) := by sorry

end IAFTRL
