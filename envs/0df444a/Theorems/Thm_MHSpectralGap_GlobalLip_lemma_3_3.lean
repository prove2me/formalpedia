-- Prove2me | Theorems.Thm_MHSpectralGap_GlobalLip_lemma_3_3
-- name    : MHSpectralGap.GlobalLip.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:52.265552+00:00
-- url     : https://prove2.me/theorems/411b2f1c-dd21-4b70-8fd9-2da41e96c891
-- title:
--   Lemma 3.3: pCN distance contraction uniformly in dimension
-- statement:
--   Under Assumptions 2.10 and 2.11, for every sufficiently small $\varepsilon>0$ there is one $c\in(0,1)$ such that both the infinite dimensional pCN kernel and every projected pCN kernel are $d_\varepsilon$-contracting:
--
--   $$W_{d_\varepsilon}(P(x,\cdot),P(y,\cdot))\le c\,d_\varepsilon(x,y)\quad\text{whenever }d_\varepsilon(x,y)<1,$$
--
--   with the analogous inequality for $P_m$ and the same $c$ for all $m$. This is the contraction input to Proposition 2.6.
--
--   **Formalization Note** “Sufficiently small” is $\exists\varepsilon_0>0\,\forall\varepsilon\in(0,\varepsilon_0]$. The finite dimensional distance is computed in the subspace norm.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, pp. 20–21, Lemma 3.3 and (3.2)

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
import Definitions.Def_MHSpectralGap_GlobalLip_Assumptions

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Lemma 3.3 with one contraction constant for every m. -/
theorem lemma_3_3 {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]
    (γ : Measure H) [IsGaussian γ] (e : HilbertBasis ℕ ℝ H)
    (hγ0 : ∫ x, x ∂γ = 0)
    (he : ∀ i j, i ≠ j → covarianceBilin γ (e i) (e j) = 0)
    (Φ : H → ℝ) (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (1 / 2 : ℝ))
    (r : ℝ → ℝ) (h210 : Assumption210 Φ δ r)
    (L : ℝ≥0) (h211 : Assumption211 Φ γ L) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Set.Ioc 0 ε₀, ∃ c : ℝ,
        IsDContracting (pcnKernel γ Φ δ) (dEps ε) c ∧
        ∀ m : ℕ, IsDContracting
          (pcnKernel (gammaM γ e m) (fun x : Km e m => Φ (x : H)) δ)
          (dEps ε) c := by sorry

end MHSpectralGap.GlobalLip
