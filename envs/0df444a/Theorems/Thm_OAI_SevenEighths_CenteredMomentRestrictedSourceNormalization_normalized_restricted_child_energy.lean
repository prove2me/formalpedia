-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentRestrictedSourceNormalization_normalized_restricted_child_energy
-- name    : OAI.SevenEighths.CenteredMomentRestrictedSourceNormalization.normalized_restricted_child_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:14:49.694007+00:00
-- url     : https://prove2.me/theorems/83af063c-bcf5-4995-b93b-a744d4e6969a
-- title:
--   Normalized restricted energy split over live allocations
-- statement:
--   Let $\iota$ be finite, $S$ as in the live-energy statement (nonzero ideals, prime on the slot part), $C$ `Supported`, $R$, $s\mid C$, profile data $\nu,W_{\mathrm{slot}},P$ ($P_i>0$), $W_1,W_2,X_1,X_2,Y_1,Y_2,B_1,B_2$, $T_{\mathrm{raw}}>0$, $f$, a predicate `keep`, a Schwartz $W$ and $K>0$ with $\operatorname{Re}W(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$. Then
--   $$\frac{\texttt{sourceRestrictedEnergy}(\mathrm{keep},\texttt{residualPool}\dots,\dots)}{T_{\mathrm{raw}}\prod_iP_i}\le|\texttt{actualAllocations}\,S\,C|\sum_B\frac{\|\texttt{frozenCoefficient}\,B\,C\,R\,\nu\,W_{\mathrm{slot}}\,P\|^2}{\texttt{rawReduction}\,B\,P}\cdot\frac{\texttt{sourceRestrictedEnergy}(\mathrm{keep},\texttt{finiteColumns}(\texttt{liveBox}\,S\,B),\texttt{liveProfile}\dots)}{\texttt{remainingRaw}\,B\,T_{\mathrm{raw}}\,P}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentRestrictedSourceNormalization.normalized_restricted_child_energy` in `lean/OAI/NumberTheory/DirichletL/Moments/RestrictedSourceNormalization.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSourceNormalization
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRestrictedSource
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentCommonRawScale CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentRestrictedSourceNormalization.instDecidableEqSumFinOfNatNat_definitions
theorem normalized_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        (‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P)*
          ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  sorry

end SevenEighths.CenteredMomentRestrictedSourceNormalization

end

end OAI
end
