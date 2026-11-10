-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_3_2
-- name    : GEPPGrowth.Main.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:13.274083+00:00
-- url     : https://prove2.me/theorems/067378ee-9673-492d-a87e-342a5eb98454
-- title:
--   Proposition 3.2 — Pivot coordinate is removed
-- statement:
--   Here $e_i$ is the pivot coordinate vector, $P_{1,i}$ swaps that coordinate with the first, and $\Pi_1$ deletes the first coordinate.
--
--   $$
--   \Pi_1P_{1,i}e_i=0
--   $$.
--
--   This identifies the pivot direction removed by compression.
--
--   Differences from the source:
--   - encoding: 1-based finite matrix and vector coordinates → zero-based Fin coordinates and explicitly translated dimensions; reason: a relabeling of every source instance; all arithmetic exponents remain real
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 3.2, printed p.7, PDF p.8

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 3.2, printed p.7 / PDF p.8. -/
theorem proposition_3_2 (d : ℕ) (i : Fin (d+1)) :
    deletion i *ᵥ basisVector i = 0 := by sorry

end GEPPGrowth.Main
