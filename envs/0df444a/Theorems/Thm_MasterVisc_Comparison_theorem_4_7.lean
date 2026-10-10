-- Prove2me | Theorems.Thm_MasterVisc_Comparison_theorem_4_7
-- name    : MasterVisc.Comparison.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:29.76007+00:00
-- url     : https://prove2.me/theorems/a1f5b18a-3f0a-4c07-9561-6673a1b6ba62
-- title:
--   Theorem 4.7, p. 961 — L-viscosity super/subsolutions are characterized by the semi-jets 𝒥̄^L, 𝒥̲^L
-- statement:
--   Let $G$ satisfy Assumption 3.1, $V\in C^0(\Theta)$ and $L>0$. Then $V$ is an $L$-viscosity supersolution of the master equation (3.1) if and only if, for every $(t,\mu)\in\Theta$,
--   $$v+G\big(t,\mu,V(t,\mu),Z,\Gamma\big)\le0\qquad\forall\,(v,Z,\Gamma)\in\overline{\mathcal J}^LV(t,\mu),$$
--   and $V$ is an $L$-viscosity subsolution if and only if $v+G(t,\mu,V(t,\mu),Z,\Gamma)\ge0$ for all $(v,Z,\Gamma)\in\underline{\mathcal J}^LV(t,\mu)$ and all $(t,\mu)\in\Theta$.
--
--   Here the semi-jets (4.6) collect the $(v,Z,\Gamma)$ — $v\in\mathbb R$, $Z,\Gamma$ $\mathcal F_t$-measurable, continuous, of linear growth — whose paraboloid $\phi^{t,V(t,\mu),v,Z,\Gamma}$ of (4.4) is a test function in $\overline{\mathcal A}^LV(t,\mu)$, resp. $\underline{\mathcal A}^LV(t,\mu)$. The theorem reduces the test-function definition to paraboloids, as in finite-dimensional viscosity theory.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 4.7, p. 961, with (4.4)–(4.6), pp. 960–961

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- Theorem 4.7, p. 961: under Assumption 3.1, `V ∈ C⁰(Θ)` is an `L`-viscosity supersolution (resp.
subsolution) iff `v + G(t, μ, V(t, μ), Z, Γ) ≤ 0` (resp. `≥ 0`) for all `(v, Z, Γ)` in the superjet
(resp. subjet) at every `(t, μ) ∈ Θ`. -/
theorem theorem_4_7 {d : ℕ} {T : ℝ≥0} (L₀ : ℝ) (G : Gen d T) (hG : Assumption31 L₀ G)
    (V : ℝ≥0 → Measure (Path d T) → ℝ) (hV : IsC0Θ V) (L : ℝ) (hL : 0 < L) :
    (IsLViscSuper L G V ↔
      ∀ (t : ℝ≥0) (μ : Measure (Path d T)) (v : ℝ) (Z : Path d T → EthierKurtz.SDEState d)
        (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ),
        t ≤ T → IsP2 μ → InJsup L V t μ v Z Γ → v + G t μ (V t μ) Z Γ ≤ 0) ∧
    (IsLViscSub L G V ↔
      ∀ (t : ℝ≥0) (μ : Measure (Path d T)) (v : ℝ) (Z : Path d T → EthierKurtz.SDEState d)
        (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ),
        t ≤ T → IsP2 μ → InJsub L V t μ v Z Γ → 0 ≤ v + G t μ (V t μ) Z Γ) := by sorry

end MasterVisc.Comparison
