-- Prove2me | Theorems.Thm_MHSpectralGap_LocalLip_theorem_2_14
-- name    : MHSpectralGap.LocalLip.theorem_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:07.443604+00:00
-- url     : https://prove2.me/theorems/28f32cf6-2807-4951-89f2-560e030b22ad
-- title:
--   Theorem 2.14, p. 13 — pCN with locally Lipschitz Φ: µ, µ_m unique invariant, and d̃(ν₁P^ñ, ν₂P^ñ) ≤ ½ d̃(ν₁, ν₂) for P and every P_m with one ñ
-- statement:
--   Let $H$ be a separable real Hilbert space carrying a centred Gaussian measure $\gamma$, and let $(e_i)_{i\ge0}$ be an orthonormal basis of eigenvectors of its covariance operator. Let $P_mH$ be the span of the first $m$ basis vectors and $\gamma_m$ the image of $\gamma$ under the orthogonal projection onto $P_mH$. Fix $\delta\in(0,\tfrac12]$ and a potential $\Phi : H\to\mathbb R$, and set
--
--   $$\mu(dx)\propto e^{-\Phi(x)}\gamma(dx),\qquad \mu_m(dx)\propto e^{-\Phi(x)}\gamma_m(dx)\ \text{ on }P_mH.$$
--
--   Let $\mathcal P$ and $\mathcal P_m$ be the pCN kernels (Algorithm 1) for $\mu$ and $\mu_m$. Assume:
--
--   1. Assumption 2.10 holds with $r(s)=r\,s^a$ for some $r>0$ and $a\in(\tfrac12,1)$;
--   2. Assumption 2.13 holds ($\exp(-\Phi)$ is $\gamma$-integrable, and the local Lipschitz constant of $\Phi$ on $B_r(0)$ is at most $M_\kappa e^{\kappa r}$ for every $\kappa>0$);
--   3. $V(x)=\|x\|^i$ with $i\in\mathbb N$, $i\ge1$, or $V(x)=\exp(v\|x\|)$ with $v>0$.
--
--   Then:
--
--   1. $\mu$ is a probability measure, it is invariant for $\mathcal P$, and it is the only invariant probability measure of $\mathcal P$; for every $m$ the same holds for $\mu_m$ and $\mathcal P_m$ on $P_mH$.
--   2. Let $d=1\wedge\bar d$ be the weighted path distance (3.6) with parameters $\eta,\varepsilon$, and $\tilde d(x,y)=\sqrt{d(x,y)(1+V(x)+V(y))}$. There is $\eta_0>0$ such that for every $\eta\in(0,\eta_0]$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$ there is $\tilde n\in\mathbb N$ with
--   $$\tilde d(\nu_1\mathcal P^{\tilde n},\nu_2\mathcal P^{\tilde n})\le\tfrac12\,\tilde d(\nu_1,\nu_2)$$
--   for all probability measures $\nu_1,\nu_2$ on $H$, and
--   $$\tilde d(\nu_1\mathcal P_m^{\tilde n},\nu_2\mathcal P_m^{\tilde n})\le\tfrac12\,\tilde d(\nu_1,\nu_2)$$
--   for every $m$ and all probability measures $\nu_1,\nu_2$ on $P_mH$ (with $d$ and $V$ restricted to $P_mH$). Here $\tilde d$ of two measures is the Wasserstein lift (2.1).
--
--   Because one $\tilde n$ serves every $m$, the pCN chains have a Wasserstein spectral gap that does not degenerate as the dimension $m$ grows, now for potentials that are only locally Lipschitz.
--
--   **Formalization Note** $\mu$ and $\mu_m$ are Mathlib's normalised tilted measures; the theorem concludes that they are probability measures (a tilted measure with non-integrable density would be the zero measure). The paper's "$r\in\mathbb R$" is read as $r>0$ (with $r=0$ the balls of (2.4) are empty), "$i\in\mathbb N$" as $i\ge1$ and $v>0$ (with $V\equiv1$ the conclusion fails for pCN). $r(s)=r s^a$ is imposed for $s\ge0$, the domain of $r$. "$\eta$ and $\varepsilon$ small enough" is read with $\eta$ chosen before $\varepsilon$, as in the proof of Lemma 3.6. The Wasserstein lifts take values in $[0,\infty]$, so the inequality is trivially true when $\tilde d(\nu_1,\nu_2)=\infty$, as on the page. The basis is indexed from $0$.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 13, Theorem 2.14

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
import Definitions.Def_MHSpectralGap_LocalLip_MHKernel
import Definitions.Def_MHSpectralGap_LocalLip_PCN
import Definitions.Def_MHSpectralGap_LocalLip_Assumption210
import Definitions.Def_MHSpectralGap_LocalLip_Assumption213
import Definitions.Def_MHSpectralGap_LocalLip_PathMetric

open MeasureTheory ProbabilityTheory

namespace MHSpectralGap.LocalLip

/-- Theorem 2.14, p. 13: under Assumptions 2.10 (with `r(s) = r s^a`, `r > 0`, `a ∈ (1/2, 1)`)
and 2.13, with `V = ‖x‖^i` (`i ≥ 1`) or `V = exp(v‖x‖)` (`v > 0`): `µ` and every `µ_m` are the
unique invariant probability measures of the pCN chains `P` and `P_m`, and for `η` and then `ε`
small enough there is one `ñ` with `d̃(ν₁P^ñ, ν₂P^ñ) ≤ ½ d̃(ν₁, ν₂)` on `H` and
`d̃(ν₁P_m^ñ, ν₂P_m^ñ) ≤ ½ d̃(ν₁, ν₂)` on every `P_m H`, where `d̃ = √(d(1 + V(x) + V(y)))` and `d`
is the path metric (3.6). -/
theorem theorem_2_14 {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (γ : Measure H) [IsGaussian γ] (hγ0 : ∫ x, x ∂γ = 0)
    (e : HilbertBasis ℕ ℝ H) (he : ∀ i j, i ≠ j → covarianceBilin γ (e i) (e j) = 0)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (1 / 2)) (Φ : H → ℝ) (r : ℝ → ℝ) (r₀ a : ℝ) (hr₀ : 0 < r₀)
    (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1) (hr : ∀ s, 0 ≤ s → r s = r₀ * s ^ a)
    (h210 : Assumption210 Φ δ r) (h213 : Assumption213 Φ γ) (V : H → ℝ)
    (hV : (∃ i : ℕ, 1 ≤ i ∧ V = fun x => ‖x‖ ^ i) ∨
      (∃ v : ℝ, 0 < v ∧ V = fun x => Real.exp (v * ‖x‖))) :
    (IsProbabilityMeasure (γ.tilted (fun x => -Φ x)) ∧
      (pcnKernel γ Φ δ).Invariant (γ.tilted (fun x => -Φ x)) ∧
      ∀ ν : Measure H, IsProbabilityMeasure ν → (pcnKernel γ Φ δ).Invariant ν →
        ν = γ.tilted (fun x => -Φ x)) ∧
    (∀ m : ℕ, IsProbabilityMeasure ((gammaM γ e m).tilted (fun x => -Φ x)) ∧
      (pcnKernel (gammaM γ e m) (fun x : Km e m => Φ x) δ).Invariant
        ((gammaM γ e m).tilted (fun x => -Φ x)) ∧
      ∀ ν : Measure (Km e m), IsProbabilityMeasure ν →
        (pcnKernel (gammaM γ e m) (fun x : Km e m => Φ x) δ).Invariant ν →
          ν = (gammaM γ e m).tilted (fun x => -Φ x)) ∧
    (∃ η₀ > 0, ∀ η ∈ Set.Ioc 0 η₀, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∃ ñ : ℕ,
      (∀ ν₁ ν₂ : Measure H, IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        MHSpectralGap.GlobalLip.wass (MHSpectralGap.GlobalLip.dTilde (dPath η ε) V) (ν₁.bind ((pcnKernel γ Φ δ ^ ñ : Kernel H H)))
            (ν₂.bind ((pcnKernel γ Φ δ ^ ñ : Kernel H H))) ≤
          (1 / 2) * MHSpectralGap.GlobalLip.wass (MHSpectralGap.GlobalLip.dTilde (dPath η ε) V) ν₁ ν₂) ∧
      ∀ (m : ℕ) (ν₁ ν₂ : Measure (Km e m)), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        MHSpectralGap.GlobalLip.wass (MHSpectralGap.GlobalLip.dTilde (fun x y : Km e m => dPath η ε (x : H) (y : H)) (fun x : Km e m => V x))
            (ν₁.bind ((pcnKernel (gammaM γ e m) (fun x : Km e m => Φ x) δ ^ ñ :
              Kernel (Km e m) (Km e m))))
            (ν₂.bind ((pcnKernel (gammaM γ e m) (fun x : Km e m => Φ x) δ ^ ñ :
              Kernel (Km e m) (Km e m)))) ≤
          (1 / 2) * MHSpectralGap.GlobalLip.wass (MHSpectralGap.GlobalLip.dTilde (fun x y : Km e m => dPath η ε (x : H) (y : H))
            (fun x : Km e m => V x)) ν₁ ν₂) := by sorry

end MHSpectralGap.LocalLip
