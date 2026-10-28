-- Prove2me | Theorems.Thm_OAI_NeutralAtom_quantum_profile_packet_limit
-- name    : OAI.NeutralAtom.quantum_profile_packet_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:18:48.695591+00:00
-- url     : https://prove2.me/theorems/0855c5b1-4e5e-4685-8e73-9874ff3dde31
-- title:
--   OAI.NeutralAtom.quantum_profile_packet_limit: intermediate lemma from OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NeutralAtom.quantum_profile_packet_limit` of [lean/OAI/Analysis/CoulombRadii/LimitTheory/TailFinish.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/LimitTheory/TailFinish.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NeutralAtom`, with `open MeasureTheory Filter Set`, `open scoped Topology BigOperators ENNReal NNReal Classical`):
--
--   ```lean
--   theorem quantum_profile_packet_limit
--       (N : ℕ → ℕ) (ψ : ∀ n,Wavefunction (N n+1))
--       (hψ : ∀ n,IsNormalizedGroundState (N n+1) (ψ n))
--       [∀ n,IsProbabilityMeasure (rawLaw (ψ n))]
--       {ε B C L M : ℝ} (hε : 0 < ε) (hB : 0 < B) (_ : 0 ≤ M)
--       (s : ℕ → ℝ) (hsp : ∀ n,0 < s n) (hs : Tendsto s atTop (𝓝 0))
--       (hN : Tendsto (fun n => N n+1) atTop atTop)
--       (hr₀ : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0))
--       (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (Cq : ℕ → ℝ)
--       (d : ∀ n,QuantumProfileDatum (ψ n) ε B C L M (s n) (q n:ℝ) (Cq n))
--       (hprob : ∀ n,Cq n*s n^25 ≤ (q n:ℝ)⁻¹)
--       {a b : ℝ} (ha : 0 < a) (hab : a < b) :
--       Tendsto (fun n => s n^3 * ∫ x,packetMass Coulomb.unitWindow 1
--         (initialAtomicRadius ε ((N n+1:ℕ):ℝ)) (s n) (spatialAnnulus (a*s n) (b*s n)) x ∂rawLaw (ψ n))
--         atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Coulomb.Space` and `OAI.Coulomb.unitWindow` (definitions bundle `OAIQ062C000` of this split); `OAI.NeutralAtom.initialAtomicRadius`, `OAI.NeutralAtom.packetMass`, `OAI.NeutralAtom.rawLaw` and `OAI.NeutralAtom.spatialAnnulus` (definitions bundle `OAIQ062C002` of this split); `OAI.NeutralAtom.QuantumProfileDatum` (definitions bundle `OAIQ062C008` of this split); `OAI.NeutralAtom.Configuration`, `OAI.NeutralAtom.IsNormalizedGroundState`, `OAI.NeutralAtom.Position` and `OAI.NeutralAtom.Wavefunction` (the published bundle `Def_CoulombRadii`).
--
--   **Used by.** The proof of `OAI.NeutralAtom.generalized_outer_radii` of this split imports it.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombRadii/LimitTheory/TailFinish.lean (declaration OAI.NeutralAtom.quantum_profile_packet_limit)

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

theorem quantum_profile_packet_limit
    (N : ℕ → ℕ) (ψ : ∀ n,Wavefunction (N n+1))
    (hψ : ∀ n,IsNormalizedGroundState (N n+1) (ψ n))
    [∀ n,IsProbabilityMeasure (rawLaw (ψ n))]
    {ε B C L M : ℝ} (hε : 0 < ε) (hB : 0 < B) (_ : 0 ≤ M)
    (s : ℕ → ℝ) (hsp : ∀ n,0 < s n) (hs : Tendsto s atTop (𝓝 0))
    (hN : Tendsto (fun n => N n+1) atTop atTop)
    (hr₀ : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0))
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (Cq : ℕ → ℝ)
    (d : ∀ n,QuantumProfileDatum (ψ n) ε B C L M (s n) (q n:ℝ) (Cq n))
    (hprob : ∀ n,Cq n*s n^25 ≤ (q n:ℝ)⁻¹)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => s n^3 * ∫ x,packetMass Coulomb.unitWindow 1
      (initialAtomicRadius ε ((N n+1:ℕ):ℝ)) (s n) (spatialAnnulus (a*s n) (b*s n)) x ∂rawLaw (ψ n))
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  sorry
end NeutralAtom
end

end

end OAI
end
