-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_peak_sprinkling_eventual_survival_bs
-- name    : OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:28:51.677176+00:00
-- url     : https://prove2.me/theorems/7cbeff8b-5f51-4b54-92d2-cdb3282c9330
-- title:
--   OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival` of [lean/OAI/Probability/BenjaminiSchramm/PeakSprinklingSurvival.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/PeakSprinklingSurvival.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology BigOperators`, `open BernoulliProduct Percolation.BenjaminiSchramm`):
--
--   ```lean
--   theorem peak_sprinkling_eventual_survival_bs
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (O : G.OrbitRepresentatives) (p q b : unitInterval)
--       (hparam : Percolation.sprinkleParameter q b=p)
--       (a : V → ℝ) (R : ℝ) (hR : 0 < R)
--       (hfin : ∀ x, ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
--       (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
--       (hgb : ∀ l, g l ≤ C₀) (hglim : Tendsto g atTop (𝓝 0))
--       (havoid : ∀ (x : V) (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
--         Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
--           (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
--             (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
--               (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
--       (c rate A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
--       (hsurv : ∀ n : ℕ, 0 < n → ENNReal.ofReal (c*Real.exp (-rate*n)) ≤
--         G.peakSurvivalProbability O a R q n)
--       (hprofile : ∀ n : ℕ, 0 < n → ∀ l : ℕ, G.peakSurvivalLayerMoment O a R q n l ≤
--         G.peakSurvivalProbability O a R q n *
--           ENNReal.ofReal (C*Real.exp (-A*max ((l : ℝ)-n) 0)))
--       (ε : ℝ) (hε : 0 < ε) :
--       ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((c/2)*Real.exp (-(rate+ε)*n)) ≤
--         G.fullPeakDownProbability O a p (R*n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BernoulliProduct.erasedWhiteParameters`, `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.adjustedLayerIndex`, `OAI.CriticalPercolation.BondGraph.cluster`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.fullPeakDownProbability`, `OAI.CriticalPercolation.BondGraph.incidentEdges`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.peakSurvivalLayerMoment`, `OAI.CriticalPercolation.BondGraph.peakSurvivalProbability` and `OAI.Percolation.BenjaminiSchramm.exteriorEscape` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.sprinkleParameter` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/PeakSprinklingSurvival.lean (declaration OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival)

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem peak_sprinkling_eventual_survival_bs
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (O : G.OrbitRepresentatives) (p q b : unitInterval)
    (hparam : Percolation.sprinkleParameter q b=p)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
    (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hgb : ∀ l, g l ≤ C₀) (hglim : Tendsto g atTop (𝓝 0))
    (havoid : ∀ (x : V) (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
      Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
        (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
          (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
            (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
    (c rate A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hsurv : ∀ n : ℕ, 0 < n → ENNReal.ofReal (c*Real.exp (-rate*n)) ≤
      G.peakSurvivalProbability O a R q n)
    (hprofile : ∀ n : ℕ, 0 < n → ∀ l : ℕ, G.peakSurvivalLayerMoment O a R q n l ≤
      G.peakSurvivalProbability O a R q n *
        ENNReal.ofReal (C*Real.exp (-A*max ((l : ℝ)-n) 0)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((c/2)*Real.exp (-(rate+ε)*n)) ≤
      G.fullPeakDownProbability O a p (R*n) := by
  sorry

end CriticalPercolation.BondGraph

end

end OAI
end
