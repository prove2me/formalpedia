-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentAmplificationLiveEnergy_original_masked_child_energy
-- name    : OAI.SevenEighths.CenteredMomentAmplificationLiveEnergy.original_masked_child_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:17:22.123281+00:00
-- url     : https://prove2.me/theorems/66ff9d81-b221-4afa-93a7-e76ab4542bbf
-- title:
--   Source Gauss energy split over live allocations
-- statement:
--   Let $\iota$ be finite, $S:\iota\oplus\mathrm{Fin}\,2\to$ finite sets of nonzero ideals of the Eisenstein integers (prime on the $\iota$ part), $C,R,s$ ideals with `Supported C` and $s$ coprime to $C$, $\nu$, $W_{\mathrm{slot}}$, $P$, $W_1,W_2$, reals $X_1,X_2,Y_1,Y_2$, ideals $B_1,B_2$, $f$, a Schwartz $W$ and $K>0$ with $\operatorname{Re}W(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$. Then the real part of the `sourceGaussEnergy` over `residualPool C _ (finiteColumns (piFinset S))` of the coefficients $I\mapsto[C,I\text{ coprime}]\cdot$`finiteColumnCoefficient (piFinset S) (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C I)` is at most
--   $$|\texttt{actualAllocations}\,S\,C|\sum_{B}\|\texttt{frozenCoefficient}\,B\,C\,R\,\nu\,W_{\mathrm{slot}}\,P\|^2\operatorname{Re}\texttt{sourceGaussEnergy}\big(\texttt{finiteColumns}(\texttt{liveBox}\,S\,B),\ \texttt{finiteColumnCoefficient}(\dots,\texttt{maskedLiveProfile}\,B\,C\,R\,s\dots),f,W,K\big).$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentAmplificationLiveEnergy.original_masked_child_energy` in `lean/OAI/NumberTheory/DirichletL/Moments/AmplificationLiveEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationLiveEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationLiveEnergy.instDecidableEqSumFinOfNatNat_definitions
theorem original_masked_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  sorry

end SevenEighths.CenteredMomentAmplificationLiveEnergy

end

end OAI
end
