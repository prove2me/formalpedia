-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_lemma_3_4
-- name    : GPhNGIDiffusion.OccupationCLT.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:36.00368+00:00
-- url     : https://prove2.me/theorems/90e2804b-e042-4bf8-b417-3a81b1139c83
-- title:
--   Lemma 3.4, p. 13 — moment bounds E|X_t|^m ≤ e^{Ct}(|x|^m + 1) uniform in ε, and E|X^ε_t − X_t|^m → 0
-- statement:
--   Let $(X^x_t)$ solve (1.1) and, for $0<\varepsilon<1$, let $(X^{\varepsilon,x}_t)$ solve the mollified equation (3.3) driven by the same Brownian motion. For every integer $m\ge2$ there is a constant $C>0$ such that for all $x\in\mathbb R^d$, $t\ge0$ and $\varepsilon\in(0,1)$,
--   $$
--   \mathbb E|X^{\varepsilon,x}_t|^m,\ \mathbb E|X^x_t|^m\le e^{Ct}(|x|^m+1),
--   $$
--   and for every integer $m\ge2$, $x$ and $t\ge0$,
--   $$
--   \mathbb E|X^{\varepsilon,x}_t-X^x_t|^m\to0\qquad(\varepsilon\to0).
--   $$
--
--   These bounds control the growth of the diffusion and justify passing from the mollified to the original equation.
--
--   **Formalization Note** The paper states (3.5) with the explicit rate $C_m=2m^2\tilde C_{op}$ of (1.10), where $\tilde C_{op}=C_{op}+\|\sigma\sigma'\|_{HS}+1+\|R-\alpha I\|_{op}+|\beta|$. That rate is false in large dimension: its proof bounds $\mathrm{tr}(\sigma\sigma')$ by $\|\sigma\sigma'\|_{HS}$, which fails by a factor up to $\sqrt d$. Counterexample: $d=10^4$, $p_i=1/d$, $P=0$, $v=e$, $\alpha=1$, $\beta=0$, $\sigma=I$ gives $g(x)=-x$, $C_2=816$, and $\mathbb E|X^0_t|^2=d(1-e^{-2t})/2\approx29.9>e^{816t}\approx11.6$ at $t=0.003$. The statement therefore keeps the form of (3.5) with a constant depending on $m$ and the model, uniform in $x$, $t$ and $\varepsilon$, which is all the rest of the paper uses. Expectations are lower Lebesgue integrals in $[0,\infty]$, so no integrability is assumed. The paper's "intergers" is its typo for "integers".
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 13, Lemma 3.4, (3.5)–(3.6) (proof p. 32)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Diffusion
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Mollified
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Lemma 3.4, p. 13, with the explicit rate `C_m = 2m²C̃_op` of (1.10) replaced by a constant
`C` depending on `m` and the model (the explicit rate fails in large dimension; see the
Formalization Note). `X^ε` solves the mollified equation (3.3) driven by the same `B`. For all
integers `m ≥ 2`: `E|X^{ε,x}_t|^m, E|X^x_t|^m ≤ e^{Ct}(|x|^m + 1)` uniformly in `x`, `t ≥ 0`,
`ε ∈ (0, 1)`; and `E|X^{ε,x}_t − X^x_t|^m → 0` as `ε → 0` (3.6). -/
theorem lemma_3_4 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (Xε : ℝ → E d → ℝ≥0 → Ω → E d)
    (hXε : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, IsSolution (M.gEps ε) M.σ B (Xε ε)) :
    (∀ m : ℕ, 2 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (x : E d) (t : ℝ≥0),
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        ∫⁻ ω, ‖Xε ε x t ω‖ₑ ^ m ∂P ≤ ENNReal.ofReal (Real.exp (C * t) * (‖x‖ ^ m + 1))) ∧
      ∫⁻ ω, ‖X x t ω‖ₑ ^ m ∂P ≤ ENNReal.ofReal (Real.exp (C * t) * (‖x‖ ^ m + 1))) ∧
    (∀ m : ℕ, 2 ≤ m → ∀ (x : E d) (t : ℝ≥0),
      Tendsto (fun ε : ℝ => ∫⁻ ω, ‖Xε ε x t ω - X x t ω‖ₑ ^ m ∂P) (𝓝[>] 0) (𝓝 0)) := by sorry

end GPhNGIDiffusion.OccupationCLT
