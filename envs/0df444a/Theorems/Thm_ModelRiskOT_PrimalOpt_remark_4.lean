-- Prove2me | Theorems.Thm_ModelRiskOT_PrimalOpt_remark_4
-- name    : ModelRiskOT.PrimalOpt.remark_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:51:04.85105+00:00
-- url     : https://prove2.me/theorems/8890a996-c0d3-4bdb-898e-3901773f0b63
-- title:
--   Remark 4, (10)–(11) — ε-optimal transport plans: I − I(π) splits into two nonnegative gaps
-- statement:
--   Let $S$ be a Polish space, $\mu$ a probability measure on $S$, $\delta>0$, and let $c$ and $f$ satisfy (A1) and (A2). Let $\lambda^*\ge0$ be such that $(\lambda^*,\varphi_{\lambda^*})\in\Lambda_{c,f}$ is a dual optimal pair: $I=J(\lambda^*,\varphi_{\lambda^*})<\infty$. Let $\varepsilon>0$ and let $\pi\in\Phi_{\mu,\delta}$ with $\int f^-(y)\,d\pi(x,y)<\infty$. Put
--   $$T_1=\int\Bigl(\varphi_{\lambda^*}(x)-\bigl(f(y)-\lambda^*c(x,y)\bigr)\Bigr)\,d\pi(x,y)\in[0,\infty],\qquad T_2=\lambda^*\Bigl(\delta-\int c\,d\pi\Bigr).$$
--   Then:
--   1. $T_2\ge0$;
--   2. (10) $\pi$ is $\varepsilon$-primal optimal, $I\le I(\pi)+\varepsilon$, if and only if $T_1+T_2\le\varepsilon$;
--   3. (11) if $I\le I(\pi)+\varepsilon$, then $T_1\le\varepsilon$ and $\lambda^*(\delta-\int c\,d\pi)\le\varepsilon$; if moreover $\lambda^*>0$,
--   $$\Bigl(\delta-\frac{\varepsilon}{\lambda^*}\Bigr)^+\le\int c\,d\pi\le\delta.$$
--
--   The two gaps measure how far $\pi$ is from moving mass to maximizers of $f(y)-\lambda^*c(x,y)$ and from using the whole budget. Proposition 9 uses (11) to show that nearly optimal plans concentrate on near-maximizers.
--
--   **Formalization Note** The paper's (11) prints the integrand as $\varphi_{\lambda^*}(x)-f(y)-\lambda^*c(x,y)$ and writes $I(\pi_\varepsilon)=\pi_\varepsilon(S\times A)$; the statement uses the integrand of (10) and $I(\pi)$, as the paper intends. The second part of (11) is also stated in the multiplied form $\lambda^*(\delta-\int c\,d\pi)\le\varepsilon$ (the form (39) uses), which covers $\lambda^*=0$, where $\varepsilon/\lambda^*$ is undefined. The hypothesis $\int f^-\,d\pi<\infty$ makes $I(\pi)$ well defined. $T_1$ is a lower integral of a nonnegative extended-real integrand; $\int c\,d\pi$ is the real value of a lower integral that is at most $\delta$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 8, Remark 4, Eqs. (10) and (11)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_Basic

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **Remark 4, (10) and (11)** (p. 8). Let `(λ*, φ_{λ*}) ∈ Λ_{c,f}` be a dual optimal pair with
`I = J(λ*, φ_{λ*}) < ∞`, let `ε > 0` and let `π ∈ Φ_{μ,δ}` with `∫ f⁻(y) dπ < ∞` (so that `I(π)` is
well defined). Write `T₁ = ∫ (φ_{λ*}(x) − (f(y) − λ* c(x, y))) dπ(x, y) ∈ [0, ∞]` and
`T₂ = λ* (δ − ∫ c dπ)`. Then `T₂ ≥ 0`; `π` is `ε`-primal optimal (`I ≤ I(π) + ε`) iff
`T₁ + T₂ ≤ ε` (10); and if `π` is `ε`-optimal then `T₁ ≤ ε`, `λ* (δ − ∫ c dπ) ≤ ε`, and, when
`λ* > 0`, `(δ − ε/λ*)⁺ ≤ ∫ c dπ ≤ δ` (11). -/
theorem remark_4 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ)
    (lam : ℝ) (hfeas : (lam, phiLam c f lam) ∈ dualFeasible c f)
    (hopt : ModelRiskOT.Duality.primalValue c f μ δ = ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam))
    (hfin : ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam) < ⊤)
    (ε : ℝ) (hε : 0 < ε) (π : Measure (S × S)) (hπ : π ∈ ModelRiskOT.Duality.primalFeasible c μ δ)
    (hπf : ∫⁻ p, ENNReal.ofReal (-f p.2) ∂π < ⊤) :
    let T₁ : ENNReal := ∫⁻ p, (phiLam c f lam p.1 -
      ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal)).toENNReal ∂π
    let C : ℝ := (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal
    let T₂ : ℝ := lam * (δ - C)
    0 ≤ T₂ ∧
    (ModelRiskOT.Duality.primalValue c f μ δ ≤ ModelRiskOT.Duality.primalObj f π + (ε : EReal) ↔
      (T₁ : EReal) + (T₂ : EReal) ≤ (ε : EReal)) ∧
    (ModelRiskOT.Duality.primalValue c f μ δ ≤ ModelRiskOT.Duality.primalObj f π + (ε : EReal) →
      T₁ ≤ ENNReal.ofReal ε ∧ lam * (δ - C) ≤ ε ∧
        (0 < lam → max (δ - ε / lam) 0 ≤ C ∧ C ≤ δ)) := by sorry

end ModelRiskOT.PrimalOpt
