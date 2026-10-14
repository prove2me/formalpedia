-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_lemma_3_6
-- name    : GPhNGIDiffusion.OccupationCLT.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:06.704207+00:00
-- url     : https://prove2.me/theorems/b3dca5f9-fedd-48c9-8532-23032451f40d
-- title:
--   Lemma 3.6, p. 15 — E|𝓘^x_u(t)|^m ≤ C|u|^m t^{−m/2} e^{mC_op t} and E|𝓘^{ε,x}_u(t) − 𝓘^x_u(t)|^m → 0
-- statement:
--   Let $\mathcal I^{\varepsilon,x}_u(t)=\frac1t\int_0^t\langle\sigma^{-1}J^{\varepsilon,x}_ru,dB_r\rangle$ and $\mathcal I^x_u(t)=\frac1t\int_0^t\langle\sigma^{-1}J^x_ru,dB_r\rangle$ (3.14), with $J_r=J_{0,r}$. For every $m\ge2$ there is a constant $C>0$ such that for all $x,u\in\mathbb R^d$, $t>0$ and $\varepsilon\in(0,1)$,
--   $$
--   \mathbb E|\mathcal I^{\varepsilon,x}_u(t)|^m,\ \mathbb E|\mathcal I^x_u(t)|^m\le\frac{C|u|^m}{t^{m/2}}e^{mC_{op}t},\tag{3.15}
--   $$
--   and for all $m\ge2$, $x,u$ and $t>0$,
--   $$
--   \lim_{\varepsilon\to0}\mathbb E|\mathcal I^{\varepsilon,x}_u(t)-\mathcal I^x_u(t)|^m=0.\tag{3.16}
--   $$
--
--   These are the integrability bounds on the Bismut–Elworthy–Li weights used in Lemma 3.3 and Proposition 3.1.
--
--   **Formalization Note** $C$ may depend on $m$ (it comes from the Burkholder–Davis–Gundy inequality) and on the model. $m$ is real. The Itô integrals are characterized by the `Ito` predicate, and the statement holds for every random variable satisfying it.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 15, Lemma 3.6, (3.15)–(3.16) (proof p. 33)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Diffusion
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Jacobian
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Ito
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Lemma 3.6, p. 15. With `I^{ε,x}_u(t) = (1/t)∫₀ᵗ⟨σ⁻¹J^{ε,x}_r u, dB_r⟩` and
`I^x_u(t) = (1/t)∫₀ᵗ⟨σ⁻¹J^x_r u, dB_r⟩` (3.14), `J_r = J_{0,r}`: for every `m ≥ 2` there is `C`
with `E|I^{ε,x}_u(t)|^m, E|I^x_u(t)|^m ≤ C|u|^m t^{−m/2} e^{mC_op t}` for all `x, u`, `t > 0`,
`ε ∈ (0, 1)` (3.15), and `E|I^{ε,x}_u(t) − I^x_u(t)|^m → 0` as `ε → 0` (3.16). -/
theorem lemma_3_6 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (Xε : ℝ → E d → ℝ≥0 → Ω → E d)
    (hXε : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, IsSolution (M.gEps ε) M.σ B (Xε ε))
    (Jε : ℝ → E d → ℝ≥0 → ℝ≥0 → Ω → (E d →L[ℝ] E d))
    (hJε : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ x ω,
      IsPropagator (fun r => M.gradEps ε (Xε ε x r ω)) (fun s t => Jε ε x s t ω))
    (J : E d → ℝ≥0 → ℝ≥0 → Ω → (E d →L[ℝ] E d))
    (hJ : ∀ x ω, IsPropagator (fun r => M.gradTilde (X x r ω)) (fun s t => J x s t ω)) :
    (∀ m : ℝ, 2 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (x u : E d) (t : ℝ≥0), 0 < t →
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ I : Ω → ℝ,
        IsItoIntegral P B (fun r ω => mat M.σ⁻¹ (Jε ε x 0 r ω u)) t I →
        ∫⁻ ω, ‖(t : ℝ)⁻¹ * I ω‖ₑ ^ m ∂P
          ≤ ENNReal.ofReal (C * ‖u‖ ^ m / (t : ℝ) ^ (m / 2) * Real.exp (m * M.Cop * t))) ∧
      (∀ I : Ω → ℝ,
        IsItoIntegral P B (fun r ω => mat M.σ⁻¹ (J x 0 r ω u)) t I →
        ∫⁻ ω, ‖(t : ℝ)⁻¹ * I ω‖ₑ ^ m ∂P
          ≤ ENNReal.ofReal (C * ‖u‖ ^ m / (t : ℝ) ^ (m / 2) * Real.exp (m * M.Cop * t)))) ∧
    (∀ m : ℝ, 2 ≤ m → ∀ (x u : E d) (t : ℝ≥0), 0 < t →
      ∀ (Iε : ℝ → Ω → ℝ) (I : Ω → ℝ),
        (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
          IsItoIntegral P B (fun r ω => mat M.σ⁻¹ (Jε ε x 0 r ω u)) t (Iε ε)) →
        IsItoIntegral P B (fun r ω => mat M.σ⁻¹ (J x 0 r ω u)) t I →
        Tendsto (fun ε : ℝ => ∫⁻ ω, ‖(t : ℝ)⁻¹ * Iε ε ω - (t : ℝ)⁻¹ * I ω‖ₑ ^ m ∂P)
          (𝓝[>] 0) (𝓝 0)) := by sorry

end GPhNGIDiffusion.OccupationCLT
