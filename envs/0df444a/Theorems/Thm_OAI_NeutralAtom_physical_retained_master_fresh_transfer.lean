-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_retained_master_fresh_transfer
-- name    : OAI.NeutralAtom.physical_retained_master_fresh_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:21:26.354636+00:00
-- url     : https://prove2.me/theorems/c048f197-5a24-4288-a151-8a84e591a2b6
-- title:
--   OAI.NeutralAtom.physical_retained_master_fresh_transfer: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_retained_master_fresh_transfer` of [lean/OAI/Analysis/CoulombRadii/Variational/RetainedMasterTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Variational/RetainedMasterTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap`):
--
--   ```lean
--   theorem physical_retained_master_fresh_transfer {D c A ε : ℝ}
--       (hD : 0≤D) (hc : 0 < c) (hA : 0<A) (hε : 0<ε) :
--       ∃ s₀ : ℝ, 0 < s₀ ∧ s₀≤1 ∧ ∀ {N J : ℕ} (Z : ℕ) (hZ : 1≤Z)
--       {ψ : Wavefunction (N+1)} {g : Gradient (N+1)}, FormDomain ψ g → normSquared ψ=1 →
--       (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
--         energy Z ψ g≤energy Z χ h) →
--       ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
--       energy Z ψ g≤E+D → ∀ {r₀ s : ℝ}, 0 < r₀ → 0 < s → s < s₀ →
--       ∀ (j : ℕ), r₀ * (2 : ℝ) ^ j ≤ s →
--       ∀ {B : Set (Fin J → UnorderedArray (N+1))}, MeasurableSet B →
--       (r₀*2^j)^42≤(observationLaw J (rawLaw ψ)).real
--         (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B) →
--       ∀ (y : Position) (hy : y≠0), r₀≤‖y‖ → Coulomb.atomicCellScale y≤A*(r₀*2^j) →
--       ∃ u : Coulomb.H1Vector (N+1), Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
--         Coulomb.form (Coulomb.atom Z hZ) u≤E+retainedInverseOffset D (r₀*2^j) ∧
--         (∀ F : Coulomb.Configuration (N+1) → ℝ, Coulomb.potentialForm F u=
--           (stateWeightedIntegral ψ (arrayEventLikelihood
--             (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
--             (retainedTailObservation j ⁻¹' B)))⁻¹*
--           stateWeightedIntegral ψ (fun x => arrayEventLikelihood
--             (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
--             (retainedTailObservation j ⁻¹' B) x*F (flattenConfiguration (N+1) x))) ∧
--       ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
--       ∃ T : Coulomb.AtomicBudgetHistory (Coulomb.atom Z hZ) u
--         (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
--         T.ensemble.totalForm (Coulomb.atom Z hZ)≤Coulomb.form (Coulomb.atom Z hZ) u+
--           Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
--         T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
--         T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
--         Coulomb.atomicPatchTFGap (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
--           ((Coulomb.atomicCellScale y)^(6/5:ℝ))
--           (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤
--           2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
--         T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
--           (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*
--             (Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
--         ∀ (g₀ : 𝓢(Position,ℝ)), (∫ w,g₀ w^2)=1 →
--         (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
--         |((Z:ℝ)*coulombKernel y-
--             potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g₀ c r₀ s) y)-
--           Coulomb.atomicPatchMeanField (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
--             ((Coulomb.atomicCellScale y)^(6/5:ℝ))
--             (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
--           ε*(Coulomb.atomicCellScale y)^(-4:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Antisymmetric`, `OAI.Coulomb.AtomicBudgetHistory`, `OAI.Coulomb.Configuration`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.Space`, `OAI.Coulomb.atomicCellScale`, `OAI.Coulomb.atomicCellScale_pos`, `OAI.Coulomb.form`, `OAI.Coulomb.mass`, `OAI.Coulomb.potentialForm`, `OAI.Coulomb.Nuclei`, `OAI.Coulomb.RecordedEnsemble.OutSupported` and `OAI.Coulomb.RecordedEnsemble.totalForm` (definitions bundle `OAIQ062C000` of this split); `OAI.NeutralAtom.coulombKernel` and `OAI.NeutralAtom.potentialOf` (definitions bundle `OAIQ062C001` of this split); `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.RetainedScales`, `OAI.NeutralAtom.UnorderedArray`, `OAI.NeutralAtom.arrayEventLikelihood`, `OAI.NeutralAtom.mixturePacketDensity`, `OAI.NeutralAtom.observationLaw`, `OAI.NeutralAtom.rawLaw`, `OAI.NeutralAtom.retainedInverseOffset`, `OAI.NeutralAtom.stateWeightedIntegral`, `OAI.NeutralAtom.tailObservation` and `OAI.NeutralAtom.unorderedArrayMeasurable` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom`, `OAI.Coulomb.atomicPatchCountFactor`, `OAI.Coulomb.thinIMS`, `OAI.Coulomb.unrestrictedFormBottom`, `OAI.NeutralAtom.flattenConfiguration`, `OAI.Coulomb.RecordedEnsemble.CoreSupported`, `OAI.Coulomb.RecordedEnsemble.OutFermionic` and `OAI.Coulomb.RecordedEnsemble.deletedSquare` (definitions bundle `OAIQ062C004` of this split); `OAI.NeutralAtom.fromH1Wave` and `OAI.NeutralAtom.retainedTailObservation` (definitions bundle `OAIQ062C007` of this split); `OAI.Coulomb.atomicCountConstant`, `OAI.Coulomb.atomicPatchMeanField` and `OAI.Coulomb.atomicPatchTFGap` (definitions bundle `OAIQ062C008` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.Position`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proof of `OAI.NeutralAtom.physical_normalized_inverse_point` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Variational/RetainedMasterTransfer.lean (declaration OAI.NeutralAtom.physical_retained_master_fresh_transfer)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

section

attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_retained_master_fresh_transfer {D c A ε : ℝ}
    (hD : 0≤D) (hc : 0 < c) (hA : 0<A) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀≤1 ∧ ∀ {N J : ℕ} (Z : ℕ) (hZ : 1≤Z)
    {ψ : Wavefunction (N+1)} {g : Gradient (N+1)}, FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → ∀ {r₀ s : ℝ}, 0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : ℕ), r₀ * (2 : ℝ) ^ j ≤ s →
    ∀ {B : Set (Fin J → UnorderedArray (N+1))}, MeasurableSet B →
    (r₀*2^j)^42≤(observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B) →
    ∀ (y : Position) (hy : y≠0), r₀≤‖y‖ → Coulomb.atomicCellScale y≤A*(r₀*2^j) →
    ∃ u : Coulomb.H1Vector (N+1), Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u≤E+retainedInverseOffset D (r₀*2^j) ∧
      (∀ F : Coulomb.Configuration (N+1) → ℝ, Coulomb.potentialForm F u=
        (stateWeightedIntegral ψ (arrayEventLikelihood
          (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
          (retainedTailObservation j ⁻¹' B)))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood
          (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
          (retainedTailObservation j ⁻¹' B) x*F (flattenConfiguration (N+1) x))) ∧
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
    ∃ T : Coulomb.AtomicBudgetHistory (Coulomb.atom Z hZ) u
      (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm (Coulomb.atom Z hZ)≤Coulomb.form (Coulomb.atom Z hZ) u+
        Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
      Coulomb.atomicPatchTFGap (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
        ((Coulomb.atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤
        2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
        (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*
          (Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
      ∀ (g₀ : 𝓢(Position,ℝ)), (∫ w,g₀ w^2)=1 →
      (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
      |((Z:ℝ)*coulombKernel y-
          potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g₀ c r₀ s) y)-
        Coulomb.atomicPatchMeanField (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
          ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        ε*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
  sorry
end NeutralAtom
end

end

end OAI
end
