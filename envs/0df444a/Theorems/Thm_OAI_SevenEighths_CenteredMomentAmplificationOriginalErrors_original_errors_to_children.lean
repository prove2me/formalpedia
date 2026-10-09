-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentAmplificationOriginalErrors_original_errors_to_children
-- name    : OAI.SevenEighths.CenteredMomentAmplificationOriginalErrors.original_errors_to_children
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:11.351776+00:00
-- url     : https://prove2.me/theorems/b331c22b-4c57-4ec7-b9c3-062284ca1f73
-- title:
--   Amplification errors bounded by child energies
-- statement:
--   Let $\eta$ be a `Character`, $m\ne0$ and $p$ prime Eisenstein integers with $(p)$ maximal, prime and `Supported`, $(p)$ avoiding `goodLambda`, residue characteristic $\ne2$, `goodLambda`$^2\mid p-1$, `goodLambda`$\mid m$, $2\mid m$, and $n\in\{0,5,6\}$. Then there is a map $\tau$ from ray characters to characters with $N(\tau(\chi).\mathrm{modulus})\le$`rowConductorBound (childCharacter η χ) m 1 (p^(2·errorMovingExponent n))` such that for every $S$ as in the live-energy statement whose $\iota$-ideals are prime and coprime to $(p)$, ideals $R,s$ with $s$ coprime to $(p)^{n+1}$, profile data, reals $t$, $T>0$, finite `rows` of elements not divisible by $p$, Schwartz $W$ and $K>0$ with $\operatorname{Re}W(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$ everywhere and $\ge1$ on `rows`: with $\beta$ the column coefficient and $C=(p)^{n+1}$,
--   $$\sum_{h\in\mathrm{rows}}\|\texttt{amplificationError}(\dots,T^{-1/2}\beta(I)\texttt{rowWeight}\,\eta\,m\,1\,1\,t\,I,\dots,p,n+1,h)\|^2\le16(n+2)\,\texttt{localErrorCost}\,p\,n\cdot\frac{\sum_\chi\sum_B\operatorname{Re}\texttt{sourceGaussEnergy}(\dots,\texttt{heightCoeff}(\tau\chi)\,t,W,K)}{T/N((p))^{n+1}}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentAmplificationOriginalErrors.original_errors_to_children` in `lean/OAI/NumberTheory/DirichletL/Moments/AmplificationOriginalErrors.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationOriginalErrors
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationGlobal
open CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy
open CenteredMomentAmplificationSourceDomain CenteredMomentOriginalChildEnergy
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationOriginalErrors.instDecidableEqSumFinOfNatNat_definitions
theorem original_errors_to_children (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0<T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  sorry

end SevenEighths.CenteredMomentAmplificationOriginalErrors

end

end OAI
end
