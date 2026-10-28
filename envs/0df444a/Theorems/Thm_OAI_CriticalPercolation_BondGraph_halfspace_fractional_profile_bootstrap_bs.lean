-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_halfspace_fractional_profile_bootstrap_bs
-- name    : OAI.CriticalPercolation.BondGraph.halfspace_fractional_profile_bootstrap_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:27:00.038277+00:00
-- url     : https://prove2.me/theorems/f2e8a0fa-e826-40be-a74a-8b62dd8e0e64
-- title:
--   OAI.CriticalPercolation.BondGraph.halfspace_fractional_profile_bootstrap_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.halfspace_fractional_profile_bootstrap` of [lean/OAI/Probability/BenjaminiSchramm/HalfspaceProfileBootstrap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/HalfspaceProfileBootstrap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`, `open Percolation.BenjaminiSchramm`):
--
--   ```lean
--   theorem halfspace_fractional_profile_bootstrap_bs [Fintype G.VertexOrbit] [Nontrivial V]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
--       (hu : ¬G.CombinatoriallyUnimodular)
--       (d : ℕ) (hd : ∀ u, (Percolation.finite_neighbors hl u).toFinset.card ≤ d)
--       (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
--         |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) u v| ≤ R)
--       (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
--       (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
--       (L U B : ℝ) (hB : 0 < B)
--       (hdown : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p R L)
--       (hup : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
--         ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
--           (∫⁻ ω, (G.adjustedSlabBandCount (G.stationaryOrbitWeight μ) (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
--             C*ENNReal.ofReal (Real.exp ((-1+ζ)*k+U*r)))
--       (hcrude : ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
--         (∫⁻ ω, (restrictedLayerCount G.ends
--           (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
--           {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
--             G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
--             C*ENNReal.ofReal (Real.exp (B*k))) :
--       ∀ q : ℝ, 0 < q → q < 1 →
--         G.downwardHalfspaceFractionalProfile (G.stationaryOrbitWeight μ) p R q ∧
--         G.upwardHalfspaceFractionalProfile (G.stationaryOrbitWeight μ) p R q
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.Percolation.finite_neighbors`, `OAI.Percolation.internalEdges`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.adjustedSlabBandCount`, `OAI.CriticalPercolation.BondGraph.downwardHalfspaceFractionalProfile`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.lowerSlabFractionalProfile`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel`, `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight`, `OAI.CriticalPercolation.BondGraph.upwardHalfspaceFractionalProfile` and `OAI.Percolation.BenjaminiSchramm.restrictedLayerCount` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.Adj` and `OAI.Percolation.cluster` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/HalfspaceProfileBootstrap.lean (declaration OAI.CriticalPercolation.BondGraph.halfspace_fractional_profile_bootstrap)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem halfspace_fractional_profile_bootstrap_bs [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular)
    (d : ℕ) (hd : ∀ u, (Percolation.finite_neighbors hl u).toFinset.card ≤ d)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) u v| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (L U B : ℝ) (hB : 0 < B)
    (hdown : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p R L)
    (hup : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount (G.stationaryOrbitWeight μ) (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ζ)*k+U*r)))
    (hcrude : ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (B*k))) :
    ∀ q : ℝ, 0 < q → q < 1 →
      G.downwardHalfspaceFractionalProfile (G.stationaryOrbitWeight μ) p R q ∧
      G.upwardHalfspaceFractionalProfile (G.stationaryOrbitWeight μ) p R q := by
  sorry

end CriticalPercolation.BondGraph

end

end OAI
end
