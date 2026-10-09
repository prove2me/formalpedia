-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyReferenceDeletionEnergy_original_energy_weighted_deletion
-- name    : OAI.SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy.original_energy_weighted_deletion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:21:25.766983+00:00
-- url     : https://prove2.me/theorems/77089c54-9261-4438-aeb2-2f97ba13c159
-- title:
--   Slot energy bounded through weighted deletions
-- statement:
--   Let $\alpha$ be finite, $b_{\mathrm{slot}},M\ge0$ on $\alpha$, $\varepsilon>0$. Then there is $C>0$ such that for every natural state $s$, Schwartz $W_1,W_2$ supported in $[a,b]$ ($a>0$, $b\ge0$), slot pools, coefficients $\beta$, sizes $P$, reals $t,X_1,X_2,E,p$: if for every pair of deleted ideal sets $D_1,D_2$ and slot subset $J$ the `radialEnergy` (of the effective state) of the products of the two deleted polynomials and the remaining natural slots is at most $E\,N(\prod D_2)^p$ (hypothesis of the Lean), then `energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂ …` $\le C\,N(\operatorname{rad}s.\mathrm{puncture})^{\varepsilon}E$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy.original_energy_weighted_deletion` in `lean/OAI/NumberTheory/DirichletL/Energy/ReferenceDeletionEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison
open CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem original_energy_weighted_deletion (bslot M:α→ℝ)(hM:∀i,0≤M i)
    (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ a b:ℝ)(s:NaturalState Z Bmask bΦ)
      (W₁ W₂:𝓢(ℝ,ℂ)),0<a → 0≤b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X₁ X₂ E p:ℝ),
      (∀i,∀I∈pool i,Prime I) → (∀i,0<P i) →
      (∀i,∀I∈pool i,‖β i I‖≤M i) →
      (∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤bslot i*P i) →
      0<X₁ → 0<X₂ → 0≤E → p≤1 →
      (∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀J∈(Finset.univ:Finset α).powerset,
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
          polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
          ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i)
            (heightCoefficient (β i) t) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
            ≤E*((∏I∈D₂,I).absNorm:ℝ)^p) →
      energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤C*(s.puncture.radical.absNorm:ℝ)^ε*E:= by
  sorry

end SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy

end

end OAI
end
