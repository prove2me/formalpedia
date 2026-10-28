-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_restricted_interpolation_measure_bs
-- name    : OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:28:14.752661+00:00
-- url     : https://prove2.me/theorems/519feee6-076f-4e66-8a27-f0d50624c9e8
-- title:
--   OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure` of [lean/OAI/Probability/CriticalPercolation/Criticality/RestrictedInterpolation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/RestrictedInterpolation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem restricted_interpolation_measure_bs (S : Set E) (hS : S.Finite)
--       (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
--       (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0 < c) (hε : 0<ε)
--       (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
--       (hconn : ∀ j k, j<k → k≤d → k-j<d →
--         c ≤ (G.law p).real {ω | (G.openGraph (S ∩ ω)).Reachable (x j) (x k)})
--       (s : ℕ) (hδ : 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s}) :
--       ∃ j<d, 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s} ∧
--         -Real.log ((G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s}) ≤
--           interpolationConstant c ε *
--             (Real.log (1/(G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s})+Nat.clog 2 d+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.openGraph` and `OAI.CriticalPercolation.BondGraph.twoClusterEvent` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.interpolationConstant` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/RestrictedInterpolation.lean (declaration OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure)

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem restricted_interpolation_measure_bs (S : Set E) (hS : S.Finite)
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0 < c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph (S ∩ ω)).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s}) :
    ∃ j<d, 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s} ∧
      -Real.log ((G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s}) ≤
        interpolationConstant c ε *
          (Real.log (1/(G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s})+Nat.clog 2 d+1) := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
