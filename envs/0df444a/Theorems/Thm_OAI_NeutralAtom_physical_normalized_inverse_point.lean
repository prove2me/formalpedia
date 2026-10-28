-- Prove2me | Theorems.Thm_OAI_NeutralAtom_physical_normalized_inverse_point
-- name    : OAI.NeutralAtom.physical_normalized_inverse_point
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:12:26.468304+00:00
-- url     : https://prove2.me/theorems/1c2b3947-845a-465b-975c-f4c9c7f89454
-- title:
--   OAI.NeutralAtom.physical_normalized_inverse_point: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.physical_normalized_inverse_point` of [lean/OAI/Analysis/CoulombRadii/Packets/NormalizedInversePoint.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Packets/NormalizedInversePoint.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap`):
--
--   ```lean
--   theorem physical_normalized_inverse_point (g₀ : 𝓢(Position,ℝ))
--       (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
--       (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
--       {D c L K hl hh ξ : ℝ} (hD : 0 ≤ D) (hc : 0 < c) (hL : 1 ≤ L)
--       (hK : 0 ≤ K) (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
--       ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
--       ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
--       ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
--       (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
--         energy Z ψ g ≤ energy Z χ h) →
--       ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
--       energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
--       c*(1+packetExponent)*s^packetExponent ≤ 1/4 → c*s^packetExponent ≤ 1/100 →
--       (4*L/100000)*s ≤ 1 → ∀ (j : Fin J),r₀*2^j.val ≤ s →
--       Real.sqrt 3*(r₀*2^j.val)^(101/100:ℝ) ≤ (r₀*2^j.val)/12 →
--       ∀ (y : Position),r₀*2^j.val ≤ ‖y‖ → ‖y‖ ≤ 4*L*(r₀*2^j.val) →
--       ∀ h∈Icc hl hh,
--       letI := rawLaw_isProbability hd.2.2.1 hn
--       let P := observationLaw J (rawLaw ψ)
--       let r := fun l : Fin J => r₀*2^l.val
--       let μ := fun z => conditionalPacketDensity P Prod.fst (tailObservation r j.val) g₀ c r₀ s
--         (tailObservation r j.val z)
--       let cnt := fun z => rawCount {x : Position | (r j)/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*(r j)} (observedOrdered r j z)
--       let f := fun z => (Z:ℝ)*coulombKernel y-potentialOf (μ z) y
--       P.real {z | cnt z ≤ K/(r j)^3 ∧ Coulomb.tfScalarDensity h ≤ ‖y‖^6*μ z y ∧ ‖y‖^4*f z ≤ h-ξ/4}
--           ≤ (r j)^42 ∧
--       P.real {z | cnt z ≤ K/(r j)^3 ∧ ‖y‖^6*μ z y ≤ Coulomb.tfScalarDensity h ∧ h+ξ/4 ≤ ‖y‖^4*f z}
--           ≤ (r j)^42
--   ```
--
--   **Definitions.** The statement is written with `OAI.NeutralAtom.coulombKernel` and `OAI.NeutralAtom.potentialOf` (definitions bundle `OAIQ062C001` of this split); `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.UnorderedArray`, `OAI.NeutralAtom.conditionalPacketDensity`, `OAI.NeutralAtom.observationLaw`, `OAI.NeutralAtom.observedOrdered`, `OAI.NeutralAtom.packetExponent`, `OAI.NeutralAtom.rawCount`, `OAI.NeutralAtom.rawLaw`, `OAI.NeutralAtom.rawLaw_isProbability`, `OAI.NeutralAtom.tailObservation` and `OAI.NeutralAtom.unorderedArrayMeasurable` (definitions bundle `OAIQ062C002` of this split); `OAI.Coulomb.atom` and `OAI.Coulomb.unrestrictedFormBottom` (definitions bundle `OAIQ062C004` of this split); `OAI.Coulomb.tfScalarDensity` and `OAI.NeutralAtom.observationLaw_probability` (definitions bundle `OAIQ062C005` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.FormDomain`, `OAI.NeutralAtom.Gradient`, `OAI.NeutralAtom.HasWeakGradient`, `OAI.NeutralAtom.IsAntisymmetric`, `OAI.NeutralAtom.Position`, `OAI.NeutralAtom.Spins`, `OAI.NeutralAtom.Wavefunction`, `OAI.NeutralAtom.energy` and `OAI.NeutralAtom.normSquared` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proofs of `OAI.NeutralAtom.physical_propagation_good_events` and `OAI.NeutralAtom.physical_tf_band` of this split import it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/Packets/NormalizedInversePoint.lean (declaration OAI.NeutralAtom.physical_normalized_inverse_point)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C004
import Definitions.Def_OAIQ062C005

section

attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_normalized_inverse_point (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {D c L K hl hh ξ : ℝ} (hD : 0 ≤ D) (hc : 0 < c) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 → c*s^packetExponent ≤ 1/100 →
    (4*L/100000)*s ≤ 1 → ∀ (j : Fin J),r₀*2^j.val ≤ s →
    Real.sqrt 3*(r₀*2^j.val)^(101/100:ℝ) ≤ (r₀*2^j.val)/12 →
    ∀ (y : Position),r₀*2^j.val ≤ ‖y‖ → ‖y‖ ≤ 4*L*(r₀*2^j.val) →
    ∀ h∈Icc hl hh,
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun l : Fin J => r₀*2^l.val
    let μ := fun z => conditionalPacketDensity P Prod.fst (tailObservation r j.val) g₀ c r₀ s
      (tailObservation r j.val z)
    let cnt := fun z => rawCount {x : Position | (r j)/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*(r j)} (observedOrdered r j z)
    let f := fun z => (Z:ℝ)*coulombKernel y-potentialOf (μ z) y
    P.real {z | cnt z ≤ K/(r j)^3 ∧ Coulomb.tfScalarDensity h ≤ ‖y‖^6*μ z y ∧ ‖y‖^4*f z ≤ h-ξ/4}
        ≤ (r j)^42 ∧
    P.real {z | cnt z ≤ K/(r j)^3 ∧ ‖y‖^6*μ z y ≤ Coulomb.tfScalarDensity h ∧ h+ξ/4 ≤ ‖y‖^4*f z}
        ≤ (r j)^42 := by
  sorry
end NeutralAtom
end

end

end OAI
end
