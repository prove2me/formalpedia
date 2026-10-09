-- Prove2me | Theorems.Thm_MHSpectralGap_LocalLip_lemma_3_6
-- name    : MHSpectralGap.LocalLip.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:59:07.521265+00:00
-- url     : https://prove2.me/theorems/badad72b-1137-482f-a971-f27df5247eea
-- title:
--   Lemma 3.6, p. 23 — d-contraction uniform in m, with a nonvanishing acceptance radius
-- statement:
--   Let $H$ be a separable real Hilbert space with a centred Gaussian measure $\gamma$ and an orthonormal basis $(e_i)$ of eigenvectors of its covariance, and let $\gamma_m$, $P_mH$ be as in (1.2). Let $\delta\in(0,\tfrac12]$, and let $\Phi : H\to\mathbb R$ satisfy Assumption 2.10 (for some $r$) and Assumption 2.13. Suppose additionally that $r(s)$ has a positive lower bound for all sufficiently large $s$. Let $\mathcal P$ be the pCN kernel on $H$ and $\mathcal P_m$ the pCN kernel on $P_mH$ (reference measure $\gamma_m$, potential $\Phi$ restricted to $P_mH$), and let $d=1\wedge\bar d$ be the path distance (3.6) with parameters $\eta,\varepsilon$.
--
--   Then there is $\eta_0>0$ such that for every $\eta\in(0,\eta_0]$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$ there is a constant $c\in(0,1)$ with
--
--   $$d(x,y)<1\ \Longrightarrow\ d(\mathcal P(x,\cdot),\mathcal P(y,\cdot))\le c\,d(x,y)\quad(x,y\in H),$$
--
--   and the same inequality, with the same $c$, for $\mathcal P_m$ and all $x,y\in P_mH$, for every $m$. Here the left-hand side is the Wasserstein lift (2.1) of $d$.
--
--   This is the contraction hypothesis of the weak Harris theorem for the locally Lipschitz case, and the step where the globally Lipschitz argument (with $d=1\wedge\|x-y\|/\varepsilon$) fails.
--
--   **Formalization Note** The paper's Assumption 2.10 permits radii shrinking to zero; then its proof does not have the uniform positive probability of the event $\{\|\sqrt{2\delta}\xi\|\le r(\|x\|)\}$ needed on p. 25. The additional lower bound repairs that gap and is satisfied by $r(s)=r_0s^a$ in Theorem 2.14. "For $d$ as in (3.6)" leaves $\eta,\varepsilon$ to be chosen; the proof chooses $\eta$ small first and then $\varepsilon$ small depending on $\eta$ (p. 23: "First we choose $R$ large, before dealing with the case when $\eta$ is small and when $\varepsilon$ is small"; p. 26: "Choosing $\kappa=\eta/2$ and $\varepsilon$ small enough"), which is the quantifier order stated. On $P_mH$ the distance is the restriction of $d$ (paths in $H$). The contraction constant is explicit so that uniformity in $m$ is "one $c$ for all $m$".
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 23, Lemma 3.6

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
import Definitions.Def_MHSpectralGap_LocalLip_MHKernel
import Definitions.Def_MHSpectralGap_LocalLip_PCN
import Definitions.Def_MHSpectralGap_LocalLip_Assumption210
import Definitions.Def_MHSpectralGap_LocalLip_Assumption213
import Definitions.Def_MHSpectralGap_LocalLip_PathMetric

open MeasureTheory ProbabilityTheory

namespace MHSpectralGap.LocalLip

/-- Lemma 3.6, p. 23, with the nonvanishing-radius condition needed for its uniform
contraction claim: under Assumptions 2.10 and 2.13, the pCN kernels `P` (on `H`) and `P_m`
(on `P_m H`) are `d`-contracting for the path metric `d` of (3.6), with one contraction constant
for all `m`, once `η` and then `ε` are small enough. -/
theorem lemma_3_6 {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (γ : Measure H) [IsGaussian γ] (hγ0 : ∫ x, x ∂γ = 0)
    (e : HilbertBasis ℕ ℝ H) (he : ∀ i j, i ≠ j → covarianceBilin γ (e i) (e j) = 0)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (1 / 2)) (Φ : H → ℝ) (r : ℝ → ℝ)
    (h210 : Assumption210 Φ δ r) (h213 : Assumption213 Φ γ)
    (hrFloor : ∃ rmin > 0, ∃ Rmin > 0, ∀ s, Rmin ≤ s → rmin ≤ r s) :
    ∃ η₀ > 0, ∀ η ∈ Set.Ioc 0 η₀, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∃ c : ℝ,
      MHSpectralGap.GlobalLip.IsDContracting (pcnKernel γ Φ δ) (dPath η ε) c ∧
        ∀ m : ℕ, MHSpectralGap.GlobalLip.IsDContracting (pcnKernel (gammaM γ e m) (fun x : Km e m => Φ x) δ)
          (fun x y : Km e m => dPath η ε (x : H) (y : H)) c := by sorry

end MHSpectralGap.LocalLip
