-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_theorem_2_2
-- name    : KurtzProtter91.Integrals.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:17:00.564983+00:00
-- url     : https://prove2.me/theorems/a7821b5b-aa75-4551-abbb-3d35900e9df6
-- title:
--   Theorem 2.2 — under C2.2(i), (Xₙ, Yₙ) ⇒ (X, Y) implies Y is a semimartingale and (Xₙ, Yₙ, ∫Xₙ dYₙ) ⇒ (X, Y, ∫X dY)
-- statement:
--   For each $n$ let $(\Omega_n,\mathcal F^n,P_n)$ be a probability space with filtration $\{\mathcal F^n_t\}$, and let $(X_n,Y_n)$ be an $\{\mathcal F^n_t\}$-adapted process with sample paths in $D_{\mathbb M^{km}\times\mathbb R^m}[0,\infty)$, where $\mathbb M^{km}$ is the space of real $k\times m$ matrices, with $Y_n$ an $\{\mathcal F^n_t\}$-semimartingale. Fix $\delta\in(0,\infty]$ and define $Y_n^\delta=Y_n-J_\delta(Y_n)$. Suppose $\{Y_n^\delta\}$ has decompositions $Y_n^\delta=M_n^\delta+A_n^\delta$ into an $\{\mathcal F^n_t\}$-local martingale and a finite-variation process satisfying
--
--   **C2.2(i)** for each $\alpha>0$ there exist stopping times $\{\tau_n^\alpha\}$ such that $P\{\tau_n^\alpha\le\alpha\}\le1/\alpha$ and $\sup_nE\big[[M_n^\delta]_{t\wedge\tau_n^\alpha}+T_{t\wedge\tau_n^\alpha}(A_n^\delta)\big]<\infty$.
--
--   Let $\int X_n\,dY_n=\int X_n(s-)\,dY_n(s)$ be the stochastic integral (1.7). If $(X_n,Y_n)\Rightarrow(X,Y)$ in the Skorohod topology on $D_{\mathbb M^{km}\times\mathbb R^m}[0,\infty)$, then $Y$ is a semimartingale with respect to a filtration to which $X$ and $Y$ are adapted, and
--   $$\Big(X_n,\,Y_n,\,\int X_n\,dY_n\Big)\Rightarrow\Big(X,\,Y,\,\int X\,dY\Big)\quad\text{in the Skorohod topology on }D_{\mathbb M^{km}\times\mathbb R^m\times\mathbb R^k}[0,\infty).$$
--
--   The theorem is the paper's main result: under the uniform control C2.2(i) on the small-jump part of the integrators, joint weak convergence of integrand and integrator carries over to the stochastic integrals. It is the basis of the paper's weak limit theorems for stochastic differential equations.
--
--   **Formalization Note** The formal statement is the distributional part of Theorem 2.2 (the last sentence, on convergence in probability, is not included). $\Rightarrow$ is convergence in distribution in coupling form, for the *pair* $(X_n,Y_n)$ and for the *triple* — one time change for all components; componentwise convergence would make the theorem false (Example 1.1). The conclusion produces a probability space with a filtration $\{\mathcal G_t\}$ carrying a copy $(\tilde X,\tilde Y)$ of $(X,Y)$, both adapted, with $\tilde Y$ a semimartingale and $\tilde Z=\int\tilde X\,d\tilde Y$ its stochastic integral, such that $(X_n,Y_n,\int X_n\,dY_n)\Rightarrow(\tilde X,\tilde Y,\tilde Z)$; the copy may live on a space with extra randomness, as in Remark 2.4. The prelimit integrals $Z_n=\int X_n\,dY_n$ are given processes characterized by (1.7) (they exist for adapted cadlag $X_n$ and semimartingale $Y_n$); the limit integral is produced in the conclusion, never assumed. C2.2(i) is read with $t$ universally quantified ("for every $t\ge0$"), stopping times chosen before $t$, and the brackets with $[M](0)=0$. The limit $(X,Y)$ is taken with cadlag paths.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1039, Theorem 2.2

import Mathlib
import Definitions.Def_EthierKurtz_IsSourceLocalMartingale
import Definitions.Def_EthierKurtz_HasCrossVariation
import Definitions.Def_KurtzProtter91_Integrals_Skorohod
import Definitions.Def_KurtzProtter91_Integrals_Semimartingale

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem theorem_2_2 {k m : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration ℝ≥0 (‹∀ n, MeasurableSpace (Ω n)› n))
    (X : ∀ n, ℝ≥0 → Ω n → Fin k → Fin m → ℝ) (Y : ∀ n, ℝ≥0 → Ω n → Fin m → ℝ)
    (hXad : ∀ n, Adapted (𝓕 n) (X n)) (hXc : ∀ n ω, IsCadlag fun t => X n t ω)
    (hY : ∀ n, IsSemimartingale (𝓕 n) (P n) (Y n)) (δ : ℝ≥0∞) (hδ : 0 < δ)
    (hC : SatisfiesC22i P 𝓕 fun n t ω => Y n t ω - Jdelta δ (fun s => Y n s ω) t)
    (Z : ∀ n, ℝ≥0 → Ω n → Fin k → ℝ) (hZ : ∀ n, HasStochIntegral (P n) (X n) (Y n) (Z n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X' : ℝ≥0 → Ω' → Fin k → Fin m → ℝ) (Y' : ℝ≥0 → Ω' → Fin m → ℝ)
    (hX'c : ∀ ω, IsCadlag fun t => X' t ω) (hY'c : ∀ ω, IsCadlag fun t => Y' t ω)
    (hconv : SkorohodConvInDist P (fun n t ω => (X n t ω, Y n t ω)) P'
      (fun t ω => (X' t ω, Y' t ω))) :
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
      (𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω''›)
      (Xt : ℝ≥0 → Ω'' → Fin k → Fin m → ℝ) (Yt : ℝ≥0 → Ω'' → Fin m → ℝ)
      (Zt : ℝ≥0 → Ω'' → Fin k → ℝ),
      IsProbabilityMeasure P'' ∧
      IdentDistrib (fun ω t => (Xt t ω, Yt t ω)) (fun ω t => (X' t ω, Y' t ω)) P'' P' ∧
      (∀ ω, IsCadlag fun t => Xt t ω) ∧
      Adapted 𝓖 Xt ∧ Adapted 𝓖 Yt ∧ IsSemimartingale 𝓖 P'' Yt ∧
      HasStochIntegral P'' Xt Yt Zt ∧
      SkorohodConvInDist P (fun n t ω => (X n t ω, Y n t ω, Z n t ω)) P''
        (fun t ω => (Xt t ω, Yt t ω, Zt t ω)) := by sorry

end KurtzProtter91.Integrals
