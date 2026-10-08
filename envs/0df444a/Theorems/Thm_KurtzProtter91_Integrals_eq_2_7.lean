-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_eq_2_7
-- name    : KurtzProtter91.Integrals.eq_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:16:44.680273+00:00
-- url     : https://prove2.me/theorems/88579447-df0b-403f-87de-cf60c2beae09
-- title:
--   (2.7), stated for a general integrand H with |H| ≤ ε — E[sup_{s≤t∧τ}|∫H dY(s)|] ≤ ε(2E[[M]_{t∧τ}]^{1/2} + E[T_{t∧τ}(A)])
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with filtration $\{\mathcal G_t\}$. Let $M$ be an $\mathbb R^m$-valued $\{\mathcal G_t\}$-local martingale with cadlag paths and bracket $[M]=\sum_j[M_j]$, let $A$ be $\mathbb R^m$-valued, $\{\mathcal G_t\}$-adapted, cadlag, with paths of finite variation on bounded intervals, and let $H$ be a $\{\mathcal G_t\}$-adapted cadlag process with values in the $k\times m$ real matrices and $|H(t)|\le\varepsilon$ for all $t$. Let $R=\int H\,d(M+A)=\int H\,dM+\int H\,dA$ (the stochastic integral (1.7)). Then for every stopping time $\tau$ and every $t\ge0$,
--   $$E\Big[\sup_{s\le t\wedge\tau}|R(s)|\Big]\le\varepsilon\Big(2\,E\big[[M]_{t\wedge\tau}\big]^{1/2}+E\big[T_{t\wedge\tau}(A)\big]\Big).$$
--
--   In the proof of Theorem 2.2 this bounds $R_n^\varepsilon=\int(X_n-X_n^\varepsilon)\,dY_n^\delta$ uniformly in $n$ through C2.2(i), which is what lets the step approximation be removed in the limit.
--
--   **Formalization Note** The page states (2.7) for $H=X_n-X_n^\varepsilon$ and $(M,A)=(M_n^\delta,A_n^\delta)$ "for any stopping time $\tau$", "with similar estimates holding for $U-U^\varepsilon$"; it is stated here for a general integrand with $|H|\le\varepsilon$. The norms, which the page does not fix, are: Euclidean on $\mathbb R^k$ for $|R|$; Frobenius $|H|=(\sum_{ij}H_{ij}^2)^{1/2}$ for the integrand; Euclidean total variation for $T(A)$; and $[M]=\sum_j[M_j]$ with $[M](0)=0$. With these the constant 2 is Doob's $L^2$ constant. $E[[M]_{t\wedge\tau}]^{1/2}$ is the square root of the expectation. All expectations are lower Lebesgue integrals in $[0,\infty]$, so an infinite right-hand side is allowed and no integrability hypothesis is needed. $t\wedge\tau=t$ when $\tau=\infty$.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1041, proof of Theorem 2.2, (2.6)–(2.7)

import Mathlib
import Definitions.Def_EthierKurtz_IsSourceLocalMartingale
import Definitions.Def_EthierKurtz_HasCrossVariation
import Definitions.Def_KurtzProtter91_Integrals_Skorohod
import Definitions.Def_KurtzProtter91_Integrals_Semimartingale

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem eq_2_7 {Ω : Type*} [MeasurableSpace Ω] {k m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M A : ℝ≥0 → Ω → Fin m → ℝ) (Q : ℝ≥0 → Ω → ℝ)
    (hM : ∀ j, EthierKurtz.IsSourceLocalMartingale P 𝓖 fun t ω => M t ω j)
    (hMc : ∀ ω, IsCadlag fun t => M t ω) (hAad : Adapted 𝓖 A)
    (hAc : ∀ ω, IsCadlag fun t => A t ω) (hAfv : HasFiniteVariation P A)
    (hQ : HasBracket P M Q) (H : ℝ≥0 → Ω → Fin k → Fin m → ℝ) (hHad : Adapted 𝓖 H)
    (hHc : ∀ ω, IsCadlag fun t => H t ω) (ε : ℝ)
    (hH : ∀ t ω, Real.sqrt (∑ i, ∑ j, H t ω i j ^ 2) ≤ ε) (R : ℝ≥0 → Ω → Fin k → ℝ)
    (hR : HasStochIntegral P H (fun t ω => M t ω + A t ω) R) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓖 τ) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ (s : ℝ≥0) (_ : s ≤ minTop t (τ ω)),
        ENNReal.ofReal (Real.sqrt (∑ i, R s ω i ^ 2))) ∂P ≤
      ENNReal.ofReal ε * (2 * (∫⁻ ω, ENNReal.ofReal (Q (minTop t (τ ω)) ω) ∂P) ^ (1 / 2 : ℝ) +
        ∫⁻ ω, eVariationOn (fun s => WithLp.toLp 2 (A s ω))
          (Set.Icc 0 (minTop t (τ ω))) ∂P) := by sorry

end KurtzProtter91.Integrals
