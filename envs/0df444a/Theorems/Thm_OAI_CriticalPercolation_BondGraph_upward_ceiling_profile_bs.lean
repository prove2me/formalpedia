-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_upward_ceiling_profile_bs
-- name    : OAI.CriticalPercolation.BondGraph.upward_ceiling_profile_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:53.714572+00:00
-- url     : https://prove2.me/theorems/a2eec0a5-8aa7-4c40-8133-23f18ff62ea1
-- title:
--   OAI.CriticalPercolation.BondGraph.upward_ceiling_profile_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.upward_ceiling_profile` of [lean/OAI/Probability/BenjaminiSchramm/UpwardCeilingProfile.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/UpwardCeilingProfile.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`, `open Percolation.BenjaminiSchramm`):
--
--   ```lean
--   theorem upward_ceiling_profile_bs [Fintype G.VertexOrbit] [Nontrivial V]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
--       (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
--         |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
--       (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
--       (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
--       (Vcoef : ℝ) (hV : 0 < Vcoef)
--       (hdown : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
--         ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
--         (∫⁻ ω, (restrictedLayerCount G.ends
--           (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
--           {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
--             G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
--           D*ENNReal.ofReal (Real.exp (ζ*k)))
--       (hzero : ∀ q : ℝ, 0 < q → q < 1 → ∃ Z : ℝ≥0∞, Z < ⊤ ∧
--         ∀ c : ℝ, 0 ≤ c → ∀ x : V,
--         (∫⁻ ω, (restrictedLayerCount G.ends
--           (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ c})
--           {v | -(2*R) ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
--             G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 2*R} ω x)^q ∂G.law p) ≤
--           Z*ENNReal.ofReal (Real.exp (Vcoef*c))) :
--       ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
--         ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
--         (∫⁻ ω, (restrictedLayerCount G.ends
--           (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k})
--           {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
--             G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
--           C*ENNReal.ofReal (Real.exp ((-1+ζ)*k))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.Percolation.internalEdges`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel`, `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` and `OAI.Percolation.BenjaminiSchramm.restrictedLayerCount` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.cluster` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_endpoint_fractional_profiles_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/UpwardCeilingProfile.lean (declaration OAI.CriticalPercolation.BondGraph.upward_ceiling_profile)

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
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem upward_ceiling_profile_bs [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (Vcoef : ℝ) (hV : 0 < Vcoef)
    (hdown : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp (ζ*k)))
    (hzero : ∀ q : ℝ, 0 < q → q < 1 → ∃ Z : ℝ≥0∞, Z < ⊤ ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ c})
        {v | -(2*R) ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 2*R} ω x)^q ∂G.law p) ≤
        Z*ENNReal.ofReal (Real.exp (Vcoef*c))) :
    ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp ((-1+ζ)*k)) := by
  sorry

end CriticalPercolation.BondGraph

end

end OAI
end
