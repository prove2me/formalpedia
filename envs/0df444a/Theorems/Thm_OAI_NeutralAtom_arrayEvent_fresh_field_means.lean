-- Prove2me | Theorems.Thm_OAI_NeutralAtom_arrayEvent_fresh_field_means
-- name    : OAI.NeutralAtom.arrayEvent_fresh_field_means
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:15:33.809965+00:00
-- url     : https://prove2.me/theorems/f380c75d-2079-41f5-8e19-5fa79e395987
-- title:
--   OAI.NeutralAtom.arrayEvent_fresh_field_means: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.arrayEvent_fresh_field_means` of [lean/OAI/Analysis/CoulombRadii/RandomFields/ObservationMeanBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/RandomFields/ObservationMeanBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap`):
--
--   ```lean
--   theorem arrayEvent_fresh_field_means (g : 𝓢(Position,ℝ))
--       (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z,g z^2)=1) :
--       ∃ C D E F K N B₀ : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧ 0<K ∧ 0<N ∧ 0<B₀ ∧
--       ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
--       c*(1+packetExponent)*s^packetExponent≤1/4 →
--       ∀ {H : Type*} [Fintype H] {n J : ℕ}
--       (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
--       {B : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
--       ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
--       (∀ f : Coulomb.Configuration n → ℝ, Coulomb.potentialForm f u=
--         (stateWeightedIntegral ψ (arrayEventLikelihood ℓ B))⁻¹*
--           stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*f (flattenConfiguration n x))) →
--       ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u → T.totalMass=1 →
--       ∀ {a b t M Qlo Qhi q L U : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
--       ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
--       T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
--       (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
--       (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
--       (∀ z∈B, rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
--         (observationArrayPositions h z)≤M) →
--       0≤L → 0≤U → 0<q → C*(2*packetWidth c r₀ s y/a)≤1 →
--       let w := packetWidth c r₀ s y
--       let θ := C*(2*w/a)
--       let δ := E*(c*(1+packetExponent)*s^packetExponent)
--       let e := Real.sqrt ((D/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
--       let G := ∑ p,Coulomb.sliceExpectation (T.vector p) (Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)
--       let V := ∑ p,Coulomb.sliceExpectation (T.vector p) (fun spin x =>
--         Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y)
--       (∀ {P : ℝ}, 0<P → N*(2*w/a)≤1/2 →
--         P≤Qlo-(B₀/w^4)*(Real.sqrt 3*ℓ h+2*b)*M →
--         Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
--         L-(L/q+2*(B₀/w^3)/P)*G-2*(N*(2*w/a))*(a^4)⁻¹≤V) ∧
--       (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
--         V≤U+((Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q)*G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Configuration`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.Nuclei`, `OAI.Coulomb.RecordedEnsemble`, `OAI.Coulomb.Space`, `OAI.Coulomb.Spins`, `OAI.Coulomb.potentialForm`, `OAI.Coulomb.sliceExpectation`, `OAI.Coulomb.thomasFermiKineticConstant`, `OAI.Coulomb.H1Vector.coreSlice`, `OAI.Coulomb.H1Vector.normalized`, `OAI.Coulomb.RecordedEnsemble.Conserves` and `OAI.Coulomb.RecordedEnsemble.totalMass` (definitions bundle `OAIQ062C000` of this split); `OAI.Coulomb.tfInteriorConstant` (definitions bundle `OAIQ062C001` of this split); `OAI.NeutralAtom.arrayEventLikelihood`, `OAI.NeutralAtom.packetExponent`, `OAI.NeutralAtom.packetKernel`, `OAI.NeutralAtom.packetWidth`, `OAI.NeutralAtom.rawCount` and `OAI.NeutralAtom.stateWeightedIntegral` (definitions bundle `OAIQ062C002` of this split); `OAI.NeutralAtom.flattenConfiguration` and `OAI.Coulomb.RecordedEnsemble.CoreSupported` (definitions bundle `OAIQ062C004` of this split); `OAI.Coulomb.tfScalarDensity` (definitions bundle `OAIQ062C005` of this split); `OAI.NeutralAtom.observationArrayPositions` (definitions bundle `OAIQ062C007` of this split); `OAI.Coulomb.patchSliceTFGap` and `OAI.Coulomb.patchTFScreenedField` (definitions bundle `OAIQ062C008` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.Position` and `OAI.NeutralAtom.Wavefunction` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proof of `OAI.NeutralAtom.physical_normalized_inverse_point` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/RandomFields/ObservationMeanBounds.lean (declaration OAI.NeutralAtom.arrayEvent_fresh_field_means)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

section

attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
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

theorem arrayEvent_fresh_field_means (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z,g z^2)=1) :
    ∃ C D E F K N B₀ : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧ 0<K ∧ 0<N ∧ 0<B₀ ∧
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {H : Type*} [Fintype H] {n J : ℕ}
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {B : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ f : Coulomb.Configuration n → ℝ, Coulomb.potentialForm f u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ B))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*f (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u → T.totalMass=1 →
    ∀ {a b t M Qlo Qhi q L U : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
    (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
    (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
    (∀ z∈B, rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    0≤L → 0≤U → 0<q → C*(2*packetWidth c r₀ s y/a)≤1 →
    let w := packetWidth c r₀ s y
    let θ := C*(2*w/a)
    let δ := E*(c*(1+packetExponent)*s^packetExponent)
    let e := Real.sqrt ((D/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
    let G := ∑ p,Coulomb.sliceExpectation (T.vector p) (Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)
    let V := ∑ p,Coulomb.sliceExpectation (T.vector p) (fun spin x =>
      Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y)
    (∀ {P : ℝ}, 0<P → N*(2*w/a)≤1/2 →
      P≤Qlo-(B₀/w^4)*(Real.sqrt 3*ℓ h+2*b)*M →
      Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
      L-(L/q+2*(B₀/w^3)/P)*G-2*(N*(2*w/a))*(a^4)⁻¹≤V) ∧
    (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
      V≤U+((Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q)*G) := by
  sorry
end NeutralAtom
end

end

end OAI
end
