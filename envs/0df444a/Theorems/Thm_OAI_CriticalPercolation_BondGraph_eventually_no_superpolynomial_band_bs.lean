-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_eventually_no_superpolynomial_band_bs
-- name    : OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:24:52.210306+00:00
-- url     : https://prove2.me/theorems/02bfd66c-d23b-4726-90b1-a01669fa60bd
-- title:
--   OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band` of [lean/OAI/Probability/CriticalPercolation/Growth/SuperpolynomialContradiction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/SuperpolynomialContradiction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology`):
--
--   ```lean
--   lemma eventually_no_superpolynomial_band_bs
--       (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
--       (hquasi : G.QuasiTransitive) (hsub : G.SubexponentialGrowth)
--       (hsuper : G.SuperpolynomialGrowth) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ≤1)
--       (ε : ℝ) (hε : 0<ε) :
--       ∀ᶠ s : ℕ in atTop, ∀ (p : unitInterval) (z : V), ε≤p → ε≤1-(p:ℝ) →
--         (Real.log s)⁻¹^2 ≤ (G.law p).real (G.clusterBand z s) →
--         (∀ v, θ/2≤(G.law p).real (G.clusterTail v s)) → False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth`, `OAI.CriticalPercolation.BondGraph.SuperpolynomialGrowth`, `OAI.CriticalPercolation.BondGraph.clusterBand`, `OAI.CriticalPercolation.BondGraph.clusterTail`, `OAI.CriticalPercolation.BondGraph.fullGraph` and `OAI.CriticalPercolation.BondGraph.law` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/SuperpolynomialContradiction.lean (declaration OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma eventually_no_superpolynomial_band_bs
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hsub : G.SubexponentialGrowth)
    (hsuper : G.SuperpolynomialGrowth) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ≤1)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ s : ℕ in atTop, ∀ (p : unitInterval) (z : V), ε≤p → ε≤1-(p:ℝ) →
      (Real.log s)⁻¹^2 ≤ (G.law p).real (G.clusterBand z s) →
      (∀ v, θ/2≤(G.law p).real (G.clusterTail v s)) → False := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
