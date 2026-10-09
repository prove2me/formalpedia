-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyFirstPhysicalNormalization_actual_physical_mass_of_columnBounds
-- name    : OAI.SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:26.281344+00:00
-- url     : https://prove2.me/theorems/629a7b10-e73d-47d1-a3dd-af875947b33f
-- title:
--   Physical mass bounded from column bounds on source blocks
-- statement:
--   Let $W$ be Schwartz, $J_1,J_2\in\mathbb N$, $\iota$ finite, $hi$ on $\iota$, reals $b_1,b_2$, $B,\xi\ge0$, $\varepsilon>0$, `lowerProduct` $>0$. Then there is $C>0$ such that for all sufficiently large $Z$: for every `Input` $s$, ideal $R$, nonzero squarefree `seed`, $|s.hi_i|\le hi_i$, $|s.b_k|\le b_k$, $a_1,a_2,K>0$ with $\mathrm{lowerProduct}\le\prod s.lo_i\cdot a_1a_2$, tests vanishing below $a_1,a_2$, `volume` $\le Z^B$, $K^{-1}\le Z^B$, and the further data of the Lean ($F$, $M_{\mathrm{decl}}$, $\ell$, $E_L,E_R$), if `ColumnBounds` holds for every nonvanishing `originalBlock` (label $p$, inactive subset $E$, source block $n$), then
--   $$\frac{\texttt{physicalMass}\,s\,R\,\mathrm{seed}\,\texttt{fixedBadMask}\,1\,W\,K\,Z\,\xi}{\texttt{volume}\,s}\le\frac{C\,F\,Z^{M_{\mathrm{decl}}+\ell+\varepsilon}}{N(\mathrm{seed})}(1+|s.t|)^{J_1+J_2}\,\texttt{profileMoment}\,J_1\,\texttt{profileMoment}\,J_2.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds` in `lean/OAI/NumberTheory/DirichletL/Energy/FirstPhysicalNormalization.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceEnergy CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceMass CenteredMomentFirstNonexceptionalWeightSum

local instance instDecidableEqSumFinOfNatNat_solutions_ra1197d_1 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
theorem actual_physical_mass_of_columnBounds (W : 𝓢(ℝ, ℂ)) (J₁ J₂ : ℕ)
    (hi : ι → ℝ) (b₁ b₂ B ξ ε lowerProduct : ℝ)
    (hB : 0 ≤ B) (hξ : 0 ≤ ξ) (hε : 0 < ε) (hlower : 0 < lowerProduct) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ s : Input ι, ∀ R seed : Ideal HeckeFamily.O,
      Squarefree seed → seed ≠ 0 → (∀ i, |s.hi i| ≤ hi i) → |s.b₁| ≤ b₁ → |s.b₂| ≤ b₂ →
      ∀ a₁ a₂ K : ℝ, 0 < a₁ → 0 < a₂ → 0 < K →
      lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂ →
      (∀ x, s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x, s.W₂ x ≠ 0 → a₂ ≤ x) →
      CenteredMomentExceptionalAmplitudePair.volume s.toData ≤ Z ^ B → K⁻¹ ≤ Z ^ B →
      ∀ (F Mdecl ell : ℝ) (lossL lossR EL ER : Fin 4 → ℝ), 0 ≤ F →
      (∀ i, 0 ≤ EL i) → (∀ j, 0 ≤ ER j) →
      (∀ i, EL i ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i)) →
      (∀ j, ER j ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j)) →
      (∀ i, lossL i ≤ ell) → (∀ j, lossR j ≤ ell) →
      (∀ p : Labels s R seed, ∀ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀ n : SourceBlocks s R seed K Z ξ p E,
        originalBlock s R seed W K Z ξ p E n ≠ 0 →
          ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val)) →
      physicalMass s R seed CenteredMomentSecondHeightFamily.fixedBadMask 1 W K Z ξ /
          CenteredMomentExceptionalAmplitudePair.volume s.toData ≤
        C * F * Z ^ (Mdecl + ell + ε) / (seed.absNorm : ℝ) *
          (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  sorry

end SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization

end

end OAI
end
