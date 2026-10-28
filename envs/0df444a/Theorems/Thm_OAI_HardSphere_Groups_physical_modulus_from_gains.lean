-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physical_modulus_from_gains
-- name    : OAI.HardSphere.Groups.physical_modulus_from_gains
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:58:00.866417+00:00
-- url     : https://prove2.me/theorems/cb7f3078-62db-4c2a-b817-007fd679c525
-- title:
--   OAI.HardSphere.Groups.physical_modulus_from_gains: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal BigOperators Topology`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice HardSphere.DyadicSkeleton`):
--
--   ```lean
--   theorem physical_modulus_from_gains {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
--       (hL : L.val=(K:ℝ)) (hK : 400≤K)
--       {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
--       (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
--       (D ell B : ℝ) (hDeq : D=(N+1:ℝ)/L.val^3) (hell : 0<ell) (hM : 0<M) (hB : 1≤B)
--       (hG : ell/(8*M)≤(G:ℝ)/D)
--       (hgain : ∀ij∈currentAdmissiblePairs K,∀g : Fin G,
--         1/(8*B)≤ measureAffinity
--           (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
--           (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)) :
--       ell/(128000*M*B)≤Phase.modulusOccupation
--         (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.Comparison.measureAffinity`, `OAI.HardSphere.DyadicSkeleton.currentAdmissiblePairs`, `OAI.HardSphere.Lattice.DiscreteTorus` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Phase.modulusOccupation` (definitions bundle `OAIQ054H001` of this split); `OAI.HardSphere.Groups.physicalGroupReference` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Direction`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length`, `OAI.HardSphere.ScalarL2`, `OAI.HardSphere.Torus` and `OAI.HardSphere.lengthPositive` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.condensation_with_mixed` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

theorem physical_modulus_from_gains {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 400≤K)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
    (D ell B : ℝ) (hDeq : D=(N+1:ℝ)/L.val^3) (hell : 0<ell) (hM : 0<M) (hB : 1≤B)
    (hG : ell/(8*M)≤(G:ℝ)/D)
    (hgain : ∀ij∈currentAdmissiblePairs K,∀g : Fin G,
      1/(8*B)≤ measureAffinity
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)) :
    ell/(128000*M*B)≤Phase.modulusOccupation
      (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
