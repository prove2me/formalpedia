-- Prove2me | Theorems.Thm_MHSpectralGap_GlobalLip_theorem_2_12
-- name    : MHSpectralGap.GlobalLip.theorem_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:07:08.340434+00:00
-- url     : https://prove2.me/theorems/32d6bee8-ded2-426a-817c-e1e5ce59414a
-- title:
--   Theorem 2.12: pCN has a Wasserstein spectral gap uniform in dimension
-- statement:
--   Let $H$ be a separable Hilbert space with centered Gaussian reference law $\gamma$ and a covariance eigenbasis. Let $\mu\propto e^{-\Phi}\gamma$ and $\mu_m\propto e^{-\Phi}\gamma_m$ be the infinite and projected targets. Suppose Assumptions 2.10–2.11 hold, the step size lies in $(0,1/2]$, and the radius and Lyapunov function fall into either case of Theorem 2.12: $r(s)=r_0s^a$ for $r_0>0$, $a\in(1/2,1)$, with $V(x)=\|x\|^i$ ($i\ge1$) or $e^{v\|x\|}$ ($v>0$); or $r(s)=r_0>0$ with $V(x)=\|x\|^i$ ($i\ge1$). The measures $\mu$ and every $\mu_m$ are the unique invariant probability measures of their pCN chains. Moreover, for every sufficiently small $\varepsilon>0$ there is a **single** $\widetilde n$ such that, for every $m$ and all probability measures on the respective state spaces,
--
--   $$W_{\widetilde d}(\nu_1P^{\widetilde n},\nu_2P^{\widetilde n})\le\tfrac12W_{\widetilde d}(\nu_1,\nu_2),\qquad W_{\widetilde d_m}(\nu_1P_m^{\widetilde n},\nu_2P_m^{\widetilde n})\le\tfrac12W_{\widetilde d_m}(\nu_1,\nu_2),$$
--
--   where $d_\varepsilon(x,y)=1\wedge\|x-y\|/\varepsilon$ and $\widetilde d(x,y)=\sqrt{d_\varepsilon(x,y)(1+V(x)+V(y))}$, with the analogous restriction to $K_m$. This is the paper's dimension uniform mixing statement.
--
--   **Formalization Note** $K_m$ is the span of the first $m$ eigenvectors and $\gamma_m$ its projected Gaussian law. “Small enough” means $\exists\varepsilon_0>0\,\forall\varepsilon\in(0,\varepsilon_0]$. The positivity conditions on $i,v,r_0$ exclude vacuous radius and constant Lyapunov functions. Probability of both tilted targets is a conclusion, ruling out Mathlib's junk zero measure.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 12, Theorem 2.12

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
import Definitions.Def_MHSpectralGap_GlobalLip_Assumptions

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 2.12: uniqueness and a dimension-uniform Wasserstein contraction for pCN. -/
theorem theorem_2_12 {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]
    (γ : Measure H) [IsGaussian γ] (e : HilbertBasis ℕ ℝ H)
    (hγ0 : ∫ x, x ∂γ = 0)
    (he : ∀ i j, i ≠ j → covarianceBilin γ (e i) (e j) = 0)
    (Φ : H → ℝ) (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (1 / 2 : ℝ))
    (r : ℝ → ℝ) (h210 : Assumption210 Φ δ r)
    (L : ℝ≥0) (h211 : Assumption211 Φ γ L)
    (V : H → ℝ) (hcase : Theorem212Case r V) :
    let μ := γ.tilted (fun x => -Φ x)
    let P := pcnKernel γ Φ δ
    (IsProbabilityMeasure μ ∧ P.Invariant μ ∧
      ∀ ν : Measure H, IsProbabilityMeasure ν → P.Invariant ν → ν = μ) ∧
    (∀ m : ℕ,
      let μm := (gammaM γ e m).tilted (fun x : Km e m => -Φ (x : H))
      let Pm := pcnKernel (gammaM γ e m) (fun x : Km e m => Φ (x : H)) δ
      IsProbabilityMeasure μm ∧ Pm.Invariant μm ∧
        ∀ ν : Measure (Km e m), IsProbabilityMeasure ν → Pm.Invariant ν → ν = μm) ∧
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc 0 ε₀, ∃ ñ : ℕ,
      (∀ ν₁ ν₂ : Measure H,
        IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        wass (dTilde (dEps ε) V)
          (ν₁.bind (P ^ ñ : Kernel H H))
          (ν₂.bind (P ^ ñ : Kernel H H)) ≤
          (1 / 2 : ℝ≥0∞) * wass (dTilde (dEps ε) V) ν₁ ν₂) ∧
      (∀ m : ℕ,
        let Pm := pcnKernel (gammaM γ e m) (fun x : Km e m => Φ (x : H)) δ
        ∀ ν₁ ν₂ : Measure (Km e m),
          IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
          wass (dTilde (dEps ε) (fun x : Km e m => V (x : H)))
            (ν₁.bind (Pm ^ ñ : Kernel (Km e m) (Km e m)))
            (ν₂.bind (Pm ^ ñ : Kernel (Km e m) (Km e m))) ≤
            (1 / 2 : ℝ≥0∞) *
              wass (dTilde (dEps ε) (fun x : Km e m => V (x : H))) ν₁ ν₂)) := by sorry

end MHSpectralGap.GlobalLip
