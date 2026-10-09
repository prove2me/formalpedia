-- Prove2me | Theorems.Thm_MHSpectralGap_GlobalLip_lemma_3_2
-- name    : MHSpectralGap.GlobalLip.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:07:05.92279+00:00
-- url     : https://prove2.me/theorems/b4f51089-4ae6-4307-bbac-8270f7d93651
-- title:
--   Lemma 3.2: uniform Lyapunov functions for pCN and its projections
-- statement:
--   Suppose the pCN acceptance assumption holds. If the radius is constant, positive powers $V(x)=\|x\|^i$ are Lyapunov functions. If the radius has the form $r_0\|x\|^a$ with $a\in(1/2,1)$, both these powers and $V(x)=e^{v\|x\|}$ are Lyapunov functions. In either case there are common $l<1$ and $K>0$ such that, for all $n$ and every $m$,
--
--   $$P^nV(x)\le l^nV(x)+K,\qquad P_m^nV(x)\le l^nV(x)+K.$$
--
--   The common constants are the drift input to the dimension uniform weak Harris argument.
--
--   **Formalization Note** The potential is assumed measurable so the pCN acceptance kernel is genuine. Here $i\ge1$ and $v>0$ exclude the constant function $V\equiv1$, which would trivialize the drift condition. The paper's unused $\kappa>0$ in case (2) is omitted.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 18, Lemma 3.2

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
import Definitions.Def_MHSpectralGap_GlobalLip_Assumptions

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory

/-- Lemma 3.2, both Lyapunov-function regimes. -/
theorem lemma_3_2 {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]
    (γ : Measure H) [IsGaussian γ] (e : HilbertBasis ℕ ℝ H)
    (hγ0 : ∫ x, x ∂γ = 0)
    (he : ∀ i j, i ≠ j → covarianceBilin γ (e i) (e j) = 0)
    (Φ : H → ℝ) (hΦ : Measurable Φ) (δ : ℝ)
    (hδ : δ ∈ Set.Ioc 0 (1 / 2 : ℝ)) (r : ℝ → ℝ)
    (h210 : Assumption210 Φ δ r) (V : H → ℝ)
    (hcase : Theorem212Case r V) :
    ∃ l K : ℝ, IsLyapunov (pcnKernel γ Φ δ) V l K ∧
      ∀ m : ℕ, IsLyapunov
        (pcnKernel (gammaM γ e m) (fun x : Km e m => Φ (x : H)) δ)
        (fun x : Km e m => V (x : H)) l K := by sorry

end MHSpectralGap.GlobalLip
