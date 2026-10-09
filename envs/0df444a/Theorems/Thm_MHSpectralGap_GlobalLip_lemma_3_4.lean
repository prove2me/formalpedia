-- Prove2me | Theorems.Thm_MHSpectralGap_GlobalLip_lemma_3_4
-- name    : MHSpectralGap.GlobalLip.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:39.864972+00:00
-- url     : https://prove2.me/theorems/31fb40a7-5eee-4f28-8c0d-f1b0afd24bc1
-- title:
--   Lemma 3.4: bounded sets are uniformly small for iterated pCN
-- statement:
--   Let $S$ be a bounded subset of the Hilbert space and let $d_\varepsilon(x,y)=1\wedge\|x-y\|/\varepsilon$ with $\varepsilon>0$. Under the standing global Lipschitz setting, there are $n$ and $s\in(0,1)$ such that
--
--   $$W_{d_\varepsilon}(P^n(x,\cdot),P^n(y,\cdot))\le s\quad(x,y\in S),$$
--
--   and the same bound holds for $P_m^n$ on $S\cap K_m$, with the same $n,s$ for every $m$. This supplies the small level set required by weak Harris.
--
--   **Formalization Note** The projected chain lives on $K_m$. The set used there is the preimage of $S$ under the subspace inclusion. The globally Lipschitz hypothesis is the section's standing condition; it bounds $\Phi$ on bounded sets.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 21, Lemma 3.4

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_Wasserstein
import Definitions.Def_MHSpectralGap_GlobalLip_Assumptions

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Lemma 3.4, bounded sets are uniformly small after n steps. -/
theorem lemma_3_4 {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]
    (γ : Measure H) [IsGaussian γ] (e : HilbertBasis ℕ ℝ H)
    (hγ0 : ∫ x, x ∂γ = 0)
    (he : ∀ i j, i ≠ j → covarianceBilin γ (e i) (e j) = 0)
    (Φ : H → ℝ) (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (1 / 2 : ℝ))
    (L : ℝ≥0) (h211 : Assumption211 Φ γ L)
    (ε : ℝ) (hε : 0 < ε) (S : Set H) (hS : Bornology.IsBounded S) :
    ∃ n : ℕ, ∃ s : ℝ,
      IsDSmall ((pcnKernel γ Φ δ) ^ n) (dEps ε) S s ∧
      ∀ m : ℕ, IsDSmall
        ((pcnKernel (gammaM γ e m) (fun x : Km e m => Φ (x : H)) δ) ^ n)
        (dEps ε) {x : Km e m | (x : H) ∈ S} s := by sorry

end MHSpectralGap.GlobalLip
