-- Prove2me | Theorems.Thm_MHSpectralGap_LocalLip_lemma_3_7
-- name    : MHSpectralGap.LocalLip.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:56:06.668766+00:00
-- url     : https://prove2.me/theorems/d908317e-3394-4c94-9de3-6582f223c54b
-- title:
--   Lemma 3.7, p. 26 — bounded sets are d-small for some P^n and P_m^n, with n and s uniform in m
-- statement:
--   Let $H$, $\gamma$, $(e_i)$, $\gamma_m$, $P_mH$, $\delta\in(0,\tfrac12]$ and the pCN kernels $\mathcal P$, $\mathcal P_m$ be as in Lemma 3.6, and let $\Phi : H\to\mathbb R$ satisfy Assumption 2.13 (the standing assumption of §3.2). Let $\eta,\varepsilon>0$ and let $d=1\wedge\bar d$ be the path distance (3.6). If $S\subset H$ is bounded, then there exist $n\in\mathbb N$ and $0<s<1$ such that for all $x,y\in S$ and all $m\in\mathbb N$ (with $x,y\in P_mH$ in the second inequality)
--
--   $$d(\mathcal P_m^n(x,\cdot),\mathcal P_m^n(y,\cdot))\le s\qquad\text{and}\qquad d(\mathcal P^n(x,\cdot),\mathcal P^n(y,\cdot))\le s,$$
--
--   where $d$ of two measures is the Wasserstein lift (2.1).
--
--   This is the smallness hypothesis of the weak Harris theorem (applied to the level set $\{V\le4K\}$ of the Lyapunov function), uniformly in the dimension.
--
--   **Formalization Note** For $\mathcal P_m$ the set is $S\cap P_mH$, viewed as a subset of $P_mH$. The lemma holds for every $\eta,\varepsilon>0$ (the page does not restrict them). Assumption 2.13 is assumed because §3.2 is written under it: it makes $\Phi$ bounded on bounded sets, which the acceptance bound in the proof (by analogy with Lemma 3.4) needs; its integrability clause is not used.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 26, Lemma 3.7

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
import Definitions.Def_MHSpectralGap_LocalLip_MHKernel
import Definitions.Def_MHSpectralGap_LocalLip_PCN
import Definitions.Def_MHSpectralGap_LocalLip_Assumption213
import Definitions.Def_MHSpectralGap_LocalLip_PathMetric

open MeasureTheory ProbabilityTheory

namespace MHSpectralGap.LocalLip

/-- Lemma 3.7, p. 26: under the standing Assumption 2.13 of §3.2, every bounded set `S` is
`d`-small for some power `P^n` and, with the same `n` and `s`, for `P_m^n` on `S ∩ P_m H`,
for every `m`, where `d` is the path metric (3.6). -/
theorem lemma_3_7 {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    (γ : Measure H) [IsGaussian γ] (hγ0 : ∫ x, x ∂γ = 0)
    (e : HilbertBasis ℕ ℝ H) (he : ∀ i j, i ≠ j → covarianceBilin γ (e i) (e j) = 0)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (1 / 2)) (Φ : H → ℝ) (h213 : Assumption213 Φ γ)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (S : Set H) (hS : Bornology.IsBounded S) :
    ∃ (n : ℕ) (s : ℝ), MHSpectralGap.GlobalLip.IsDSmall (pcnKernel γ Φ δ ^ n) (dPath η ε) S s ∧
      ∀ m : ℕ, MHSpectralGap.GlobalLip.IsDSmall (pcnKernel (gammaM γ e m) (fun x : Km e m => Φ x) δ ^ n)
        (fun x y : Km e m => dPath η ε (x : H) (y : H)) {x : Km e m | (x : H) ∈ S} s := by sorry

end MHSpectralGap.LocalLip
