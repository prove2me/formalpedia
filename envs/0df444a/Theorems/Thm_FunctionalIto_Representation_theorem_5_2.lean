-- Prove2me | Theorems.Thm_FunctionalIto_Representation_theorem_5_2
-- name    : FunctionalIto.Representation.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:16.414204+00:00
-- url     : https://prove2.me/theorems/5741d64d-0d01-4292-aad4-cc8588bb7615
-- title:
--   Theorem 5.2, p. 16 — martingale representation (44): Y(T) = Y(0) + ∫₀ᵀ ∇ₓF_t(X_t, A_t) dX(t) for Y = F(X, A), F ∈ ℂ_b^{1,2}
-- statement:
--   Work under Assumption 5.1: $X(t)=X(0)+\int_0^t\sigma(u)\cdot dW(u)$ for a standard $d$-dimensional Brownian motion $W$ and an $\mathcal F^W$-progressive matrix process $\sigma$ with $\det\sigma\neq0$ a.e., $E\int_0^T\|\sigma\|^2dt<\infty$, filtration $\mathcal F=\mathcal F^X$, and $[X]=\int A\,dt$ with $A$ cadlag. Let $H$ be an $\mathcal F_T$-measurable random variable with $E|H|<\infty$ and $Y(t)=E[H\mid\mathcal F_t]$. Suppose that $Y(t)=F_t(X_t,A_t)$ a.s. for every $t<T$, for some $F\in\mathbb C_b^{1,2}([0,T))$ verifying (10). Then
--   $$Y(T)=Y(0)+\int_0^T\nabla_xF_t(X_t,A_t)\,dX(t)=Y(0)+\int_0^T\nabla_XY\cdot dX.\tag{44}$$
--
--   Precisely:
--   1. for every $t<T$, the dyadic left Riemann sums
--   $$\sum_{k<2^n}\nabla_xF_{kt/2^n}(X,A)\cdot\big(X((k+1)t/2^n)-X(kt/2^n)\big)$$
--   converge in probability to $F_t(X_t,A_t)-F_0(X_0,A_0)$;
--   2. $F_t(X_t,A_t)\to H$ in probability as $t\uparrow T$.
--
--   This is a nonanticipative counterpart of the Clark–Haussmann–Ocone formula: the integrand is computed pathwise from a functional representation of the martingale. It is used to prove the integration by parts formula on $D(X)$ (Proposition 5.5).
--
--   **Formalization Note.** The functional is given only on $[0,T)$, so the integral up to $T$ is improper: (44) is the conjunction of items 1 and 2. The Itô integral $\int_0^t\nabla_xF\,dX$ is encoded as the limit in probability of dyadic left sums (`EthierKurtz.itoStepSum`); for a left-continuous, adapted, locally bounded integrand, as $\nabla_xF_u(X_u,A_u)$ is here, this limit is the Itô integral. The standing hypotheses of the mission ($E[X](T)<\infty$, $\mathcal F=\mathcal F^X$) are included; the second makes $\mathcal F_T=\mathcal F_{T-}$, which is what makes item 2 true.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 16, Theorem 5.2, (44); context p. 15, Assumption 5.1 and p. 16, "Consider an ℱ_T measurable random variable H …"

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_FunctionalIto_Representation_Setting
import Definitions.Def_FunctionalIto_Representation_L2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

theorem theorem_5_2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (W : ℝ≥0 → Ω → EthierKurtz.SDEState d) (𝒢 ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (X : ℝ≥0 → Ω → (Fin d → ℝ))
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (hS : IsBrownianSetting P T W 𝒢 σ X ℱ A)
    (H : Ω → ℝ) (hHm : StronglyMeasurable[ℱ T] H) (hHi : Integrable H P)
    (F DF : Functional d ℝ) (gradF : Functional d (Fin d → ℝ))
    (hessF : Functional d (Matrix (Fin d) (Fin d) ℝ))
    (hF : IsC12b T F DF gradF hessF) (h10 : PredictableInV T F)
    (hY : ∀ t < T, P[H | ℱ t] =ᵐ[P] fun ω => F t (fun s => X s ω) (fun s => A s ω)) :
    (∀ t < T, TendstoInMeasure P
      (fun n ω => ∑ i, EthierKurtz.itoStepSum (fun s ω => X s ω i) t n
        (fun k ω => gradF ((k : ℝ≥0) * t / 2 ^ n) (fun s => X s ω) (fun s => A s ω) i) ω)
      atTop
      (fun ω => F t (fun s => X s ω) (fun s => A s ω) - F 0 (fun s => X s ω) (fun s => A s ω))) ∧
    TendstoInMeasure P (fun t ω => F t (fun s => X s ω) (fun s => A s ω)) (𝓝[<] T) H := by sorry

end FunctionalIto.Representation
